import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3600 : PairBound 9 := { available := 392, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 162 37 56 84 33 456 392 392), lower := (rows 67 162 37 56 84 33 64 128 256), losses := [] }

theorem u3600 : Upper (D 8) (R 8) [66,160,33,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3601 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 67 162 37 56 84 40 449 385 385), lower := (rows 67 162 37 56 84 40 64 128 256), losses := [] }

theorem u3601 : Upper (D 8) (R 8) [66,160,33,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3601 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3602 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 56 84 160 329 393 265), lower := (rows 67 162 37 56 84 160 64 128 256), losses := [] }

theorem u3602 : Upper (D 8) (R 8) [66,160,33,48,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3603 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 162 37 56 84 288 201 137 393), lower := (rows 67 162 37 56 84 288 64 128 256), losses := [] }

theorem u3603 : Upper (D 8) (R 8) [66,160,33,48,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3603 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3604 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 56 148 33 328 456 328), lower := (rows 67 162 37 56 148 33 64 128 256), losses := [] }

theorem u3604 : Upper (D 8) (R 8) [66,160,33,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3605 : PairBound 9 := { available := 321, camps := [], pairs := [], upper := (rows 67 162 37 56 148 40 321 449 321), lower := (rows 67 162 37 56 148 40 64 128 256), losses := [] }

theorem u3605 : Upper (D 8) (R 8) [66,160,33,48,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3605 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3606 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 56 148 96 329 393 265), lower := (rows 67 162 37 56 148 96 64 128 256), losses := [] }

theorem u3606 : Upper (D 8) (R 8) [66,160,33,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3607 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 67 162 37 56 148 288 73 201 329), lower := (rows 67 162 37 56 148 288 64 128 256), losses := [] }

theorem u3607 : Upper (D 8) (R 8) [66,160,33,48,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3607 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3608 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 56 208 33 332 396 268), lower := (rows 67 162 37 56 208 33 64 128 256), losses := [] }

theorem u3608 : Upper (D 8) (R 8) [66,160,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3608 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3609 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 67 162 37 56 208 36 329 393 265), lower := (rows 67 162 37 56 208 36 64 128 256), losses := [] }

theorem u3609 : Upper (D 8) (R 8) [66,160,33,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3609 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3610 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 67 162 37 56 208 40 325 389 261), lower := (rows 67 162 37 56 208 40 64 128 256), losses := [] }

theorem u3610 : Upper (D 8) (R 8) [66,160,33,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3610 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3611 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 67 162 37 56 208 288 77 141 269), lower := (rows 67 162 37 56 208 288 64 128 256), losses := [] }

theorem u3611 : Upper (D 8) (R 8) [66,160,33,48,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3611 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3612 : PairBound 9 := { available := 200, camps := [], pairs := [], upper := (rows 67 162 37 56 273 36 200 200 456), lower := (rows 67 162 37 56 273 36 64 128 256), losses := [] }

theorem u3612 : Upper (D 8) (R 8) [66,160,33,48,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3612 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3613 : PairBound 9 := { available := 196, camps := [], pairs := [], upper := (rows 67 162 37 56 273 40 196 196 452), lower := (rows 67 162 37 56 273 40 64 128 256), losses := [] }

theorem u3613 : Upper (D 8) (R 8) [66,160,33,48,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3613 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3614 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 56 273 96 204 140 396), lower := (rows 67 162 37 56 273 96 64 128 256), losses := [] }

theorem u3614 : Upper (D 8) (R 8) [66,160,33,48,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3614 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3615 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 56 273 160 76 204 332), lower := (rows 67 162 37 56 273 160 64 128 256), losses := [] }

theorem u3615 : Upper (D 8) (R 8) [66,160,33,48,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3615 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3616 : PairBound 9 := { available := 200, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 56 276 33 200 200 456), lower := (rows 67 162 37 56 276 33 64 128 256), losses := [] }

theorem u3616 : Upper (D 8) (R 8) [66,160,33,48,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3616 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3617 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 162 37 56 276 40 193 193 449), lower := (rows 67 162 37 56 276 40 64 128 256), losses := [] }

theorem u3617 : Upper (D 8) (R 8) [66,160,33,48,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3617 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3618 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 56 276 96 201 137 393), lower := (rows 67 162 37 56 276 96 64 128 256), losses := [] }

theorem u3618 : Upper (D 8) (R 8) [66,160,33,48,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3619 : PairBound 9 := { available := 73, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 56 276 160 73 201 329), lower := (rows 67 162 37 56 276 160 64 128 256), losses := [] }

theorem u3619 : Upper (D 8) (R 8) [66,160,33,48,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3620 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 194, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 56 280 33 196 196 452), lower := (rows 67 162 37 56 280 33 64 128 256), losses := [] }

theorem u3620 : Upper (D 8) (R 8) [66,160,33,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3620 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3621 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 67 162 37 56 280 36 193 193 449), lower := (rows 67 162 37 56 280 36 64 128 256), losses := [] }

theorem u3621 : Upper (D 8) (R 8) [66,160,33,48,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3621 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3622 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 130, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 56 280 96 197 133 389), lower := (rows 67 162 37 56 280 96 64 128 256), losses := [] }

theorem u3622 : Upper (D 8) (R 8) [66,160,33,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3623 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 56 280 160 69 197 325), lower := (rows 67 162 37 56 280 160 64 128 256), losses := [] }

theorem u3623 : Upper (D 8) (R 8) [66,160,33,48,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3623 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3624 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 56 336 33 204 140 396), lower := (rows 67 162 37 56 336 33 64 128 256), losses := [] }

theorem u3624 : Upper (D 8) (R 8) [66,160,33,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3625 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 162 37 56 336 36 201 137 393), lower := (rows 67 162 37 56 336 36 64 128 256), losses := [] }

theorem u3625 : Upper (D 8) (R 8) [66,160,33,48,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3625 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3626 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 162 37 56 336 40 197 133 389), lower := (rows 67 162 37 56 336 40 64 128 256), losses := [] }

theorem u3626 : Upper (D 8) (R 8) [66,160,33,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3626 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3627 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 56 336 160 77 141 269), lower := (rows 67 162 37 56 336 160 64 128 256), losses := [] }

theorem u3627 : Upper (D 8) (R 8) [66,160,33,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3628 : PairBound 9 := { available := 76, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 56 400 33 76 204 332), lower := (rows 67 162 37 56 400 33 64 128 256), losses := [] }

theorem u3628 : Upper (D 8) (R 8) [66,160,33,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3629 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 67 162 37 56 400 36 73 201 329), lower := (rows 67 162 37 56 400 36 64 128 256), losses := [] }

theorem u3629 : Upper (D 8) (R 8) [66,160,33,48,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3629 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3630 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 67 162 37 56 400 40 69 197 325), lower := (rows 67 162 37 56 400 40 64 128 256), losses := [] }

theorem u3630 : Upper (D 8) (R 8) [66,160,33,48,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3630 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3631 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 56 400 96 77 141 269), lower := (rows 67 162 37 56 400 96 64 128 256), losses := [] }

theorem u3631 : Upper (D 8) (R 8) [66,160,33,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3632 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 76 152 33 368 432 304), lower := (rows 67 162 37 76 152 33 64 128 256), losses := [] }

theorem u3632 : Upper (D 8) (R 8) [66,160,33,68,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3633 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 162 37 76 152 48 353 417 289), lower := (rows 67 162 37 76 152 48 64 128 256), losses := [] }

theorem u3633 : Upper (D 8) (R 8) [66,160,33,68,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3633 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3634 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 37 76 152 288 113 177 305), lower := (rows 67 162 37 76 152 288 64 128 256), losses := [] }

theorem u3634 : Upper (D 8) (R 8) [66,160,33,68,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3634 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3635 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 67 162 37 76 273 40 240 176 432), lower := (rows 67 162 37 76 273 40 64 128 256), losses := [] }

theorem u3635 : Upper (D 8) (R 8) [66,160,33,68,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3635 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3636 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 67 162 37 76 273 48 232 168 424), lower := (rows 67 162 37 76 273 48 64 128 256), losses := [] }

theorem u3636 : Upper (D 8) (R 8) [66,160,33,68,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3636 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3637 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 76 273 160 120 184 312), lower := (rows 67 162 37 76 273 160 64 128 256), losses := [] }

theorem u3637 : Upper (D 8) (R 8) [66,160,33,68,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3638 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 76 280 33 240 176 432), lower := (rows 67 162 37 76 280 33 64 128 256), losses := [] }

theorem u3638 : Upper (D 8) (R 8) [66,160,33,68,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3638 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3639 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 162 37 76 280 48 225 161 417), lower := (rows 67 162 37 76 280 48 64 128 256), losses := [] }

theorem u3639 : Upper (D 8) (R 8) [66,160,33,68,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3639 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3640 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 76 280 160 113 177 305), lower := (rows 67 162 37 76 280 160 64 128 256), losses := [] }

theorem u3640 : Upper (D 8) (R 8) [66,160,33,68,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3640 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3641 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 76 304 33 216 152 408), lower := (rows 67 162 37 76 304 33 64 128 256), losses := [] }

theorem u3641 : Upper (D 8) (R 8) [66,160,33,68,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3641 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3642 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 162 37 76 304 40 209 145 401), lower := (rows 67 162 37 76 304 40 64 128 256), losses := [] }

theorem u3642 : Upper (D 8) (R 8) [66,160,33,68,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3642 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3643 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 162 37 76 304 48 201 137 393), lower := (rows 67 162 37 76 304 48 64 128 256), losses := [] }

theorem u3643 : Upper (D 8) (R 8) [66,160,33,68,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3643 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3644 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 76 304 160 89 153 281), lower := (rows 67 162 37 76 304 160 64 128 256), losses := [] }

theorem u3644 : Upper (D 8) (R 8) [66,160,33,68,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3645 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 76 400 33 120 184 312), lower := (rows 67 162 37 76 400 33 64 128 256), losses := [] }

theorem u3645 : Upper (D 8) (R 8) [66,160,33,68,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3646 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 37 76 400 40 113 177 305), lower := (rows 67 162 37 76 400 40 64 128 256), losses := [] }

theorem u3646 : Upper (D 8) (R 8) [66,160,33,68,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3646 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3647 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 162 37 76 400 48 105 169 297), lower := (rows 67 162 37 76 400 48 64 128 256), losses := [] }

theorem u3647 : Upper (D 8) (R 8) [66,160,33,68,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3647 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3648 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 88 148 33 360 424 296), lower := (rows 67 162 37 88 148 33 64 128 256), losses := [] }

theorem u3648 : Upper (D 8) (R 8) [66,160,33,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3649 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 67 162 37 88 148 40 353 417 289), lower := (rows 67 162 37 88 148 40 64 128 256), losses := [] }

theorem u3649 : Upper (D 8) (R 8) [66,160,33,80,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3649 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3650 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 162 37 88 148 288 105 169 297), lower := (rows 67 162 37 88 148 288 64 128 256), losses := [] }

theorem u3650 : Upper (D 8) (R 8) [66,160,33,80,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3650 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3651 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 67 162 37 88 273 36 232 168 424), lower := (rows 67 162 37 88 273 36 64 128 256), losses := [] }

theorem u3651 : Upper (D 8) (R 8) [66,160,33,80,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3651 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3652 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 67 162 37 88 273 40 228 164 420), lower := (rows 67 162 37 88 273 40 64 128 256), losses := [] }

theorem u3652 : Upper (D 8) (R 8) [66,160,33,80,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3652 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3653 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 88 273 160 108 172 300), lower := (rows 67 162 37 88 273 160 64 128 256), losses := [] }

theorem u3653 : Upper (D 8) (R 8) [66,160,33,80,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3654 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 88 276 33 232 168 424), lower := (rows 67 162 37 88 276 33 64 128 256), losses := [] }

theorem u3654 : Upper (D 8) (R 8) [66,160,33,80,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3655 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 162 37 88 276 40 225 161 417), lower := (rows 67 162 37 88 276 40 64 128 256), losses := [] }

theorem u3655 : Upper (D 8) (R 8) [66,160,33,80,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3655 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3656 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 88 276 160 105 169 297), lower := (rows 67 162 37 88 276 160 64 128 256), losses := [] }

theorem u3656 : Upper (D 8) (R 8) [66,160,33,80,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3656 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3657 : PairBound 9 := { available := 140, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 88 304 33 204 140 396), lower := (rows 67 162 37 88 304 33 64 128 256), losses := [] }

theorem u3657 : Upper (D 8) (R 8) [66,160,33,80,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3657 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3658 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 162 37 88 304 36 201 137 393), lower := (rows 67 162 37 88 304 36 64 128 256), losses := [] }

theorem u3658 : Upper (D 8) (R 8) [66,160,33,80,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3658 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3659 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 162 37 88 304 40 197 133 389), lower := (rows 67 162 37 88 304 40 64 128 256), losses := [] }

theorem u3659 : Upper (D 8) (R 8) [66,160,33,80,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3659 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3659
end Delivery.IrregularNine14.P08

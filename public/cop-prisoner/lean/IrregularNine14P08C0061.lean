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

def b3660 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 88 304 160 77 141 269), lower := (rows 67 162 37 88 304 160 64 128 256), losses := [] }

theorem u3660 : Upper (D 8) (R 8) [66,160,33,80,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3661 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 88 400 33 108 172 300), lower := (rows 67 162 37 88 400 33 64 128 256), losses := [] }

theorem u3661 : Upper (D 8) (R 8) [66,160,33,80,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3662 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 162 37 88 400 36 105 169 297), lower := (rows 67 162 37 88 400 36 64 128 256), losses := [] }

theorem u3662 : Upper (D 8) (R 8) [66,160,33,80,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3662 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3663 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 162 37 88 400 40 101 165 293), lower := (rows 67 162 37 88 400 40 64 128 256), losses := [] }

theorem u3663 : Upper (D 8) (R 8) [66,160,33,80,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3663 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3664 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 104 148 33 344 408 280), lower := (rows 67 162 37 104 148 33 64 128 256), losses := [] }

theorem u3664 : Upper (D 8) (R 8) [66,160,33,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3664 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3665 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 67 162 37 104 148 40 337 401 273), lower := (rows 67 162 37 104 148 40 64 128 256), losses := [] }

theorem u3665 : Upper (D 8) (R 8) [66,160,33,96,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3665 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3666 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 67 162 37 104 148 48 329 393 265), lower := (rows 67 162 37 104 148 48 64 128 256), losses := [] }

theorem u3666 : Upper (D 8) (R 8) [66,160,33,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3666 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3667 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 162 37 104 148 288 89 153 281), lower := (rows 67 162 37 104 148 288 64 128 256), losses := [] }

theorem u3667 : Upper (D 8) (R 8) [66,160,33,96,132,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3667 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3668 : PairBound 9 := { available := 276, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 104 152 33 340 404 276), lower := (rows 67 162 37 104 152 33 64 128 256), losses := [] }

theorem u3668 : Upper (D 8) (R 8) [66,160,33,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3669 : PairBound 9 := { available := 273, camps := [], pairs := [], upper := (rows 67 162 37 104 152 36 337 401 273), lower := (rows 67 162 37 104 152 36 64 128 256), losses := [] }

theorem u3669 : Upper (D 8) (R 8) [66,160,33,96,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3669 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3670 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 67 162 37 104 152 48 325 389 261), lower := (rows 67 162 37 104 152 48 64 128 256), losses := [] }

theorem u3670 : Upper (D 8) (R 8) [66,160,33,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3670 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3671 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 67 162 37 104 152 288 85 149 277), lower := (rows 67 162 37 104 152 288 64 128 256), losses := [] }

theorem u3671 : Upper (D 8) (R 8) [66,160,33,96,136,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3671 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3672 : PairBound 9 := { available := 152, camps := [], pairs := [], upper := (rows 67 162 37 104 273 36 216 152 408), lower := (rows 67 162 37 104 273 36 64 128 256), losses := [] }

theorem u3672 : Upper (D 8) (R 8) [66,160,33,96,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3672 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3673 : PairBound 9 := { available := 148, camps := [], pairs := [], upper := (rows 67 162 37 104 273 40 212 148 404), lower := (rows 67 162 37 104 273 40 64 128 256), losses := [] }

theorem u3673 : Upper (D 8) (R 8) [66,160,33,96,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3673 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3674 : PairBound 9 := { available := 140, camps := [], pairs := [], upper := (rows 67 162 37 104 273 48 204 140 396), lower := (rows 67 162 37 104 273 48 64 128 256), losses := [] }

theorem u3674 : Upper (D 8) (R 8) [66,160,33,96,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3674 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3675 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 104 273 160 92 156 284), lower := (rows 67 162 37 104 273 160 64 128 256), losses := [] }

theorem u3675 : Upper (D 8) (R 8) [66,160,33,96,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3676 : PairBound 9 := { available := 152, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 104 276 33 216 152 408), lower := (rows 67 162 37 104 276 33 64 128 256), losses := [] }

theorem u3676 : Upper (D 8) (R 8) [66,160,33,96,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3676 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3677 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 162 37 104 276 40 209 145 401), lower := (rows 67 162 37 104 276 40 64 128 256), losses := [] }

theorem u3677 : Upper (D 8) (R 8) [66,160,33,96,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3677 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3678 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 67 162 37 104 276 48 201 137 393), lower := (rows 67 162 37 104 276 48 64 128 256), losses := [] }

theorem u3678 : Upper (D 8) (R 8) [66,160,33,96,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3678 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3679 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 104 276 160 89 153 281), lower := (rows 67 162 37 104 276 160 64 128 256), losses := [] }

theorem u3679 : Upper (D 8) (R 8) [66,160,33,96,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3679 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3680 : PairBound 9 := { available := 148, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 104 280 33 212 148 404), lower := (rows 67 162 37 104 280 33 64 128 256), losses := [] }

theorem u3680 : Upper (D 8) (R 8) [66,160,33,96,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3680 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3681 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 67 162 37 104 280 36 209 145 401), lower := (rows 67 162 37 104 280 36 64 128 256), losses := [] }

theorem u3681 : Upper (D 8) (R 8) [66,160,33,96,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3681 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3682 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 67 162 37 104 280 48 197 133 389), lower := (rows 67 162 37 104 280 48 64 128 256), losses := [] }

theorem u3682 : Upper (D 8) (R 8) [66,160,33,96,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3682 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3683 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 349, targets := 128 }], pairs := [(0,7)], upper := (rows 67 162 37 104 280 160 85 149 277), lower := (rows 67 162 37 104 280 160 64 128 256), losses := [] }

theorem u3683 : Upper (D 8) (R 8) [66,160,33,96,264,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3683 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3684 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 104 400 33 92 156 284), lower := (rows 67 162 37 104 400 33 64 128 256), losses := [] }

theorem u3684 : Upper (D 8) (R 8) [66,160,33,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3684 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3685 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 162 37 104 400 36 89 153 281), lower := (rows 67 162 37 104 400 36 64 128 256), losses := [] }

theorem u3685 : Upper (D 8) (R 8) [66,160,33,96,384,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3685 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3686 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 67 162 37 104 400 40 85 149 277), lower := (rows 67 162 37 104 400 40 64 128 256), losses := [] }

theorem u3686 : Upper (D 8) (R 8) [66,160,33,96,384,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3686 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3687 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 67 162 37 104 400 48 77 141 269), lower := (rows 67 162 37 104 400 48 64 128 256), losses := [] }

theorem u3687 : Upper (D 8) (R 8) [66,160,33,96,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3687 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3688 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 67 162 37 140 273 40 112 240 368), lower := (rows 67 162 37 140 273 40 64 128 256), losses := [] }

theorem u3688 : Upper (D 8) (R 8) [66,160,33,132,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3688 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3689 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 67 162 37 140 273 48 104 232 360), lower := (rows 67 162 37 140 273 48 64 128 256), losses := [] }

theorem u3689 : Upper (D 8) (R 8) [66,160,33,132,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3689 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3690 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 140 273 96 120 184 312), lower := (rows 67 162 37 140 273 96 64 128 256), losses := [] }

theorem u3690 : Upper (D 8) (R 8) [66,160,33,132,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3690 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3691 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 140 280 33 112 240 368), lower := (rows 67 162 37 140 280 33 64 128 256), losses := [] }

theorem u3691 : Upper (D 8) (R 8) [66,160,33,132,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3691 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3692 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 162 37 140 280 48 97 225 353), lower := (rows 67 162 37 140 280 48 64 128 256), losses := [] }

theorem u3692 : Upper (D 8) (R 8) [66,160,33,132,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3692 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3693 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 140 280 96 113 177 305), lower := (rows 67 162 37 140 280 96 64 128 256), losses := [] }

theorem u3693 : Upper (D 8) (R 8) [66,160,33,132,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3693 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3694 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 140 304 33 88 216 344), lower := (rows 67 162 37 140 304 33 64 128 256), losses := [] }

theorem u3694 : Upper (D 8) (R 8) [66,160,33,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3694 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3695 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 67 162 37 140 304 40 81 209 337), lower := (rows 67 162 37 140 304 40 64 128 256), losses := [] }

theorem u3695 : Upper (D 8) (R 8) [66,160,33,132,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3695 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3696 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 67 162 37 140 304 48 73 201 329), lower := (rows 67 162 37 140 304 48 64 128 256), losses := [] }

theorem u3696 : Upper (D 8) (R 8) [66,160,33,132,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3696 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3697 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 140 304 96 89 153 281), lower := (rows 67 162 37 140 304 96 64 128 256), losses := [] }

theorem u3697 : Upper (D 8) (R 8) [66,160,33,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3697 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3698 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 140 336 33 120 184 312), lower := (rows 67 162 37 140 336 33 64 128 256), losses := [] }

theorem u3698 : Upper (D 8) (R 8) [66,160,33,132,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3698 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3699 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 37 140 336 40 113 177 305), lower := (rows 67 162 37 140 336 40 64 128 256), losses := [] }

theorem u3699 : Upper (D 8) (R 8) [66,160,33,132,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3699 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3700 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 162 37 140 336 48 105 169 297), lower := (rows 67 162 37 140 336 48 64 128 256), losses := [] }

theorem u3700 : Upper (D 8) (R 8) [66,160,33,132,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3700 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3701 : PairBound 9 := { available := 104, camps := [], pairs := [], upper := (rows 67 162 37 152 273 36 104 232 360), lower := (rows 67 162 37 152 273 36 64 128 256), losses := [] }

theorem u3701 : Upper (D 8) (R 8) [66,160,33,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3701 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3702 : PairBound 9 := { available := 100, camps := [], pairs := [], upper := (rows 67 162 37 152 273 40 100 228 356), lower := (rows 67 162 37 152 273 40 64 128 256), losses := [] }

theorem u3702 : Upper (D 8) (R 8) [66,160,33,144,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3702 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3703 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 152 273 96 108 172 300), lower := (rows 67 162 37 152 273 96 64 128 256), losses := [] }

theorem u3703 : Upper (D 8) (R 8) [66,160,33,144,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3703 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3704 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 152 276 33 104 232 360), lower := (rows 67 162 37 152 276 33 64 128 256), losses := [] }

theorem u3704 : Upper (D 8) (R 8) [66,160,33,144,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3704 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3705 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 162 37 152 276 40 97 225 353), lower := (rows 67 162 37 152 276 40 64 128 256), losses := [] }

theorem u3705 : Upper (D 8) (R 8) [66,160,33,144,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3705 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3706 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 152 276 96 105 169 297), lower := (rows 67 162 37 152 276 96 64 128 256), losses := [] }

theorem u3706 : Upper (D 8) (R 8) [66,160,33,144,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3706 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3707 : PairBound 9 := { available := 76, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 152 304 33 76 204 332), lower := (rows 67 162 37 152 304 33 64 128 256), losses := [] }

theorem u3707 : Upper (D 8) (R 8) [66,160,33,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3707 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3708 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 67 162 37 152 304 36 73 201 329), lower := (rows 67 162 37 152 304 36 64 128 256), losses := [] }

theorem u3708 : Upper (D 8) (R 8) [66,160,33,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3708 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3709 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 67 162 37 152 304 40 69 197 325), lower := (rows 67 162 37 152 304 40 64 128 256), losses := [] }

theorem u3709 : Upper (D 8) (R 8) [66,160,33,144,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3709 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3710 : PairBound 9 := { available := 13, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 162 37 152 304 96 77 141 269), lower := (rows 67 162 37 152 304 96 64 128 256), losses := [] }

theorem u3710 : Upper (D 8) (R 8) [66,160,33,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3710 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3711 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 152 336 33 108 172 300), lower := (rows 67 162 37 152 336 33 64 128 256), losses := [] }

theorem u3711 : Upper (D 8) (R 8) [66,160,33,144,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3711 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3712 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 162 37 152 336 36 105 169 297), lower := (rows 67 162 37 152 336 36 64 128 256), losses := [] }

theorem u3712 : Upper (D 8) (R 8) [66,160,33,144,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3712 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3713 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 162 37 152 336 40 101 165 293), lower := (rows 67 162 37 152 336 40 64 128 256), losses := [] }

theorem u3713 : Upper (D 8) (R 8) [66,160,33,144,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3713 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3714 : PairBound 9 := { available := 56, camps := [], pairs := [], upper := (rows 67 162 37 200 273 36 120 184 312), lower := (rows 67 162 37 200 273 36 64 128 256), losses := [] }

theorem u3714 : Upper (D 8) (R 8) [66,160,33,192,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3714 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3715 : PairBound 9 := { available := 52, camps := [], pairs := [], upper := (rows 67 162 37 200 273 40 116 180 308), lower := (rows 67 162 37 200 273 40 64 128 256), losses := [] }

theorem u3715 : Upper (D 8) (R 8) [66,160,33,192,257,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3715 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3716 : PairBound 9 := { available := 44, camps := [], pairs := [], upper := (rows 67 162 37 200 273 48 108 172 300), lower := (rows 67 162 37 200 273 48 64 128 256), losses := [] }

theorem u3716 : Upper (D 8) (R 8) [66,160,33,192,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3716 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3717 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 162 37 200 276 33 120 184 312), lower := (rows 67 162 37 200 276 33 64 128 256), losses := [] }

theorem u3717 : Upper (D 8) (R 8) [66,160,33,192,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3717 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3718 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 162 37 200 276 40 113 177 305), lower := (rows 67 162 37 200 276 40 64 128 256), losses := [] }

theorem u3718 : Upper (D 8) (R 8) [66,160,33,192,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3718 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3719 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 162 37 200 276 48 105 169 297), lower := (rows 67 162 37 200 276 48 64 128 256), losses := [] }

theorem u3719 : Upper (D 8) (R 8) [66,160,33,192,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3719 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u3719
end Delivery.IrregularNine14.P08

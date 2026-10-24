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

def b720 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 104 152 160 96 145 273), lower := (rows 259 38 69 104 152 160 96 128 256), losses := [] }

theorem u720 : Upper (D 8) (R 8) [258,36,65,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b720 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b721 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 259 38 76 41 112 160 65 144 400), lower := (rows 259 38 76 41 112 160 65 128 256), losses := [] }

theorem u721 : Upper (D 8) (R 8) [258,36,72,33,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b721 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b722 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 38 76 41 112 160 80 129 385), lower := (rows 259 38 76 41 112 160 80 128 256), losses := [] }

theorem u722 : Upper (D 8) (R 8) [258,36,72,33,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b722 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b723 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 41 112 160 192 145 273), lower := (rows 259 38 76 41 112 160 192 128 256), losses := [] }

theorem u723 : Upper (D 8) (R 8) [258,36,72,33,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b723 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b724 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 178, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 41 208 160 65 176 304), lower := (rows 259 38 76 41 208 160 65 128 256), losses := [] }

theorem u724 : Upper (D 8) (R 8) [258,36,72,33,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b724 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b725 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 76 41 208 160 80 161 289), lower := (rows 259 38 76 41 208 160 80 128 256), losses := [] }

theorem u725 : Upper (D 8) (R 8) [258,36,72,33,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b725 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b726 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 41 208 160 96 145 273), lower := (rows 259 38 76 41 208 160 96 128 256), losses := [] }

theorem u726 : Upper (D 8) (R 8) [258,36,72,33,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b726 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b727 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 142, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 168 112 33 65 144 400), lower := (rows 259 38 76 168 112 33 65 128 256), losses := [] }

theorem u727 : Upper (D 8) (R 8) [258,36,72,160,96,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b727 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b728 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 38 76 168 112 33 80 129 385), lower := (rows 259 38 76 168 112 33 80 128 256), losses := [] }

theorem u728 : Upper (D 8) (R 8) [258,36,72,160,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b728 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b729 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 168 112 33 192 145 273), lower := (rows 259 38 76 168 112 33 192 128 256), losses := [] }

theorem u729 : Upper (D 8) (R 8) [258,36,72,160,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b729 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b730 : PairBound 9 := { available := 48, camps := [], pairs := [(2,5)], upper := (rows 259 38 76 168 208 33 65 176 304), lower := (rows 259 38 76 168 208 33 65 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 24 0 97 128 256), good := (rows 323 70 92 220 208 65 65 128 256) }] }

theorem u730 : Upper (D 8) (R 8) [258,36,72,160,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b730 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b731 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 76 168 208 33 80 161 289), lower := (rows 259 38 76 168 208 33 80 128 256), losses := [] }

theorem u731 : Upper (D 8) (R 8) [258,36,72,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b731 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b732 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 76 168 208 33 96 145 273), lower := (rows 259 38 76 168 208 33 96 128 256), losses := [] }

theorem u732 : Upper (D 8) (R 8) [258,36,72,160,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b732 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b733 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 259 38 196 25 112 33 72 160 416), lower := (rows 259 38 196 25 112 33 72 128 256), losses := [] }

theorem u733 : Upper (D 8) (R 8) [258,36,192,17,96,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b733 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b734 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 120, targets := 128 }], pairs := [(3,7)], upper := (rows 259 38 196 25 112 33 96 136 392), lower := (rows 259 38 196 25 112 33 96 128 256), losses := [] }

theorem u734 : Upper (D 8) (R 8) [258,36,192,17,96,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b734 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b735 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 196 25 112 33 192 168 296), lower := (rows 259 38 196 25 112 33 192 128 256), losses := [] }

theorem u735 : Upper (D 8) (R 8) [258,36,192,17,96,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b735 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b736 : PairBound 9 := { available := 40, camps := [], pairs := [(2,5)], upper := (rows 259 38 196 88 176 33 65 168 296), lower := (rows 259 38 196 88 176 33 65 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 97 128 256), good := (rows 323 70 196 92 220 65 65 128 256) }] }

theorem u736 : Upper (D 8) (R 8) [258,36,192,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b736 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b737 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 38 196 88 176 33 72 161 289), lower := (rows 259 38 196 88 176 33 72 128 256), losses := [] }

theorem u737 : Upper (D 8) (R 8) [258,36,192,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b737 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b738 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 70, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 196 88 176 33 96 137 265), lower := (rows 259 38 196 88 176 33 96 128 256), losses := [] }

theorem u738 : Upper (D 8) (R 8) [258,36,192,80,160,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b738 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b739 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 150, targets := 1 }], pairs := [(1,0)], upper := (rows 259 38 196 104 176 33 65 152 280), lower := (rows 259 38 196 104 176 33 65 128 256), losses := [] }

theorem u739 : Upper (D 8) (R 8) [258,36,192,96,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b739 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b740 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 38 196 104 176 33 72 145 273), lower := (rows 259 38 196 104 176 33 72 128 256), losses := [] }

theorem u740 : Upper (D 8) (R 8) [258,36,192,96,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b740 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b741 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 259 38 196 104 176 33 80 137 265), lower := (rows 259 38 196 104 176 33 80 128 256), losses := [] }

theorem u741 : Upper (D 8) (R 8) [258,36,192,96,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b741 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b742 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 184, targets := 1 }], pairs := [(3,0)], upper := (rows 259 70 37 104 152 160 65 176 304), lower := (rows 259 70 37 104 152 160 65 128 256), losses := [] }

theorem u742 : Upper (D 8) (R 8) [258,68,33,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b742 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b743 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 37 104 152 160 80 161 289), lower := (rows 259 70 37 104 152 160 80 128 256), losses := [] }

theorem u743 : Upper (D 8) (R 8) [258,68,33,96,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b743 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b744 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 37 104 152 160 96 145 273), lower := (rows 259 70 37 104 152 160 96 128 256), losses := [] }

theorem u744 : Upper (D 8) (R 8) [258,68,33,96,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b744 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b745 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 44 25 176 96 65 160 416), lower := (rows 259 70 44 25 176 96 65 128 256), losses := [] }

theorem u745 : Upper (D 8) (R 8) [258,68,40,17,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b745 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b746 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 44 25 176 96 96 129 385), lower := (rows 259 70 44 25 176 96 96 128 256), losses := [] }

theorem u746 : Upper (D 8) (R 8) [258,68,40,17,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b746 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b747 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 128 }], pairs := [(0,7)], upper := (rows 259 70 44 25 176 96 192 161 289), lower := (rows 259 70 44 25 176 96 192 128 256), losses := [] }

theorem u747 : Upper (D 8) (R 8) [258,68,40,17,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b747 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b748 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 259 70 44 137 176 96 65 176 304), lower := (rows 259 70 44 137 176 96 65 128 256), losses := [] }

theorem u748 : Upper (D 8) (R 8) [258,68,40,129,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b748 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b749 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 44 137 176 96 80 161 289), lower := (rows 259 70 44 137 176 96 80 128 256), losses := [] }

theorem u749 : Upper (D 8) (R 8) [258,68,40,129,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b749 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b750 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 102, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 44 137 176 96 96 145 273), lower := (rows 259 70 44 137 176 96 96 128 256), losses := [] }

theorem u750 : Upper (D 8) (R 8) [258,68,40,129,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b750 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b751 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 259 70 164 56 208 33 65 168 296), lower := (rows 259 70 164 56 208 33 65 128 256), losses := [] }

theorem u751 : Upper (D 8) (R 8) [258,68,160,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b751 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b752 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 164 56 208 33 72 161 289), lower := (rows 259 70 164 56 208 33 72 128 256), losses := [] }

theorem u752 : Upper (D 8) (R 8) [258,68,160,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b752 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b753 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 164 56 208 33 96 137 265), lower := (rows 259 70 164 56 208 33 96 128 256), losses := [] }

theorem u753 : Upper (D 8) (R 8) [258,68,160,48,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b753 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b754 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 150, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 164 104 152 33 65 176 304), lower := (rows 259 70 164 104 152 33 65 128 256), losses := [] }

theorem u754 : Upper (D 8) (R 8) [258,68,160,96,136,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b754 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b755 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 70 164 104 152 33 80 161 289), lower := (rows 259 70 164 104 152 33 80 128 256), losses := [] }

theorem u755 : Upper (D 8) (R 8) [258,68,160,96,136,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b755 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b756 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 259 70 164 104 152 33 96 145 273), lower := (rows 259 70 164 104 152 33 96 128 256), losses := [] }

theorem u756 : Upper (D 8) (R 8) [258,68,160,96,136,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b756 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b757 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 259 98 13 56 208 33 68 160 416), lower := (rows 259 98 13 56 208 33 68 128 256), losses := [] }

theorem u757 : Upper (D 8) (R 8) [258,96,9,48,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b757 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b758 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 56 208 33 96 132 388), lower := (rows 259 98 13 56 208 33 96 128 256), losses := [] }

theorem u758 : Upper (D 8) (R 8) [258,96,9,48,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b758 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b759 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 13 56 208 33 192 164 292), lower := (rows 259 98 13 56 208 33 192 128 256), losses := [] }

theorem u759 : Upper (D 8) (R 8) [258,96,9,48,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b759 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b760 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 259 98 13 168 208 33 68 176 304), lower := (rows 259 98 13 168 208 33 68 128 256), losses := [] }

theorem u760 : Upper (D 8) (R 8) [258,96,9,160,192,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b760 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b761 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 259 98 13 168 208 33 80 164 292), lower := (rows 259 98 13 168 208 33 80 128 256), losses := [] }

theorem u761 : Upper (D 8) (R 8) [258,96,9,160,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b761 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b762 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 13 168 208 33 96 148 276), lower := (rows 259 98 13 168 208 33 96 128 256), losses := [] }

theorem u762 : Upper (D 8) (R 8) [258,96,9,160,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b762 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b763 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 259 98 37 56 84 160 65 136 392), lower := (rows 259 98 37 56 84 160 65 128 256), losses := [] }

theorem u763 : Upper (D 8) (R 8) [258,96,33,48,68,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b763 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b764 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 98 37 56 84 160 72 129 385), lower := (rows 259 98 37 56 84 160 72 128 256), losses := [] }

theorem u764 : Upper (D 8) (R 8) [258,96,33,48,68,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b764 [(6,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b765 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 37 56 84 160 192 137 265), lower := (rows 259 98 37 56 84 160 192 128 256), losses := [] }

theorem u765 : Upper (D 8) (R 8) [258,96,33,48,68,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b765 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b766 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 259 98 37 76 152 160 65 176 304), lower := (rows 259 98 37 76 152 160 65 128 256), losses := [] }

theorem u766 : Upper (D 8) (R 8) [258,96,33,68,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b766 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b767 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 98 37 76 152 160 80 161 289), lower := (rows 259 98 37 76 152 160 80 128 256), losses := [] }

theorem u767 : Upper (D 8) (R 8) [258,96,33,68,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b767 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b768 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 37 76 152 160 96 145 273), lower := (rows 259 98 37 76 152 160 96 128 256), losses := [] }

theorem u768 : Upper (D 8) (R 8) [258,96,33,68,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b768 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b769 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 156, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 88 176 33 65 132 388), lower := (rows 259 98 44 88 176 33 65 128 256), losses := [] }

theorem u769 : Upper (D 8) (R 8) [258,96,40,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b769 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b770 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 98 44 88 176 33 68 129 385), lower := (rows 259 98 44 88 176 33 68 128 256), losses := [] }

theorem u770 : Upper (D 8) (R 8) [258,96,40,80,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b770 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b771 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 44 88 176 33 192 133 261), lower := (rows 259 98 44 88 176 33 192 128 256), losses := [] }

theorem u771 : Upper (D 8) (R 8) [258,96,40,80,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b771 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b772 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 259 98 44 200 145 33 68 176 304), lower := (rows 259 98 44 200 145 33 68 128 256), losses := [] }

theorem u772 : Upper (D 8) (R 8) [258,96,40,192,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b772 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b773 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 259 98 44 200 145 33 80 164 292), lower := (rows 259 98 44 200 145 33 80 128 256), losses := [] }

theorem u773 : Upper (D 8) (R 8) [258,96,40,192,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b773 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b774 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0)], upper := (rows 259 98 44 200 145 33 96 148 276), lower := (rows 259 98 44 200 145 33 96 128 256), losses := [] }

theorem u774 : Upper (D 8) (R 8) [258,96,40,192,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b774 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b775 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 156, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 200 176 33 65 148 276), lower := (rows 259 98 44 200 176 33 65 128 256), losses := [] }

theorem u775 : Upper (D 8) (R 8) [258,96,40,192,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b775 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b776 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 259 98 44 200 176 33 68 145 273), lower := (rows 259 98 44 200 176 33 68 128 256), losses := [] }

theorem u776 : Upper (D 8) (R 8) [258,96,40,192,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b776 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b777 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 259 98 44 200 176 33 80 133 261), lower := (rows 259 98 44 200 176 33 80 128 256), losses := [] }

theorem u777 : Upper (D 8) (R 8) [258,96,40,192,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b777 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b778 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 150, targets := 1 }], pairs := [(1,0)], upper := (rows 259 194 28 104 176 33 65 164 292), lower := (rows 259 194 28 104 176 33 65 128 256), losses := [] }

theorem u778 : Upper (D 8) (R 8) [258,192,24,96,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b778 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b779 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 194 28 104 176 33 68 161 289), lower := (rows 259 194 28 104 176 33 68 128 256), losses := [] }

theorem u779 : Upper (D 8) (R 8) [258,192,24,96,160,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b779 [(6,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u779
end Delivery.IrregularNine14.P08

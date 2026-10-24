import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b5700 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 194 28 73 145 288 66 164 292), lower := (rows 35 194 28 73 145 288 66 128 256), losses := [] }

theorem u5700 : Upper (D 7) (R 7) [34,192,24,65,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5700 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5701 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 130 }], pairs := [(2,1),(2,7)], upper := (rows 35 194 28 73 145 288 68 162 290), lower := (rows 35 194 28 73 145 288 68 128 256), losses := [] }

theorem u5701 : Upper (D 7) (R 7) [34,192,24,65,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5701 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5702 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 35 194 28 73 145 288 96 134 262), lower := (rows 35 194 28 73 145 288 96 128 256), losses := [] }

theorem u5702 : Upper (D 7) (R 7) [34,192,24,65,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5702 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5703 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 35 194 28 73 176 288 65 134 262), lower := (rows 35 194 28 73 176 288 65 128 256), losses := [] }

theorem u5703 : Upper (D 7) (R 7) [34,192,24,65,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5703 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5704 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 194 28 73 176 288 66 133 261), lower := (rows 35 194 28 73 176 288 66 128 256), losses := [] }

theorem u5704 : Upper (D 7) (R 7) [34,192,24,65,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5704 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5705 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 28 73 176 288 68 131 259), lower := (rows 35 194 28 73 176 288 68 128 256), losses := [] }

theorem u5705 : Upper (D 7) (R 7) [34,192,24,65,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5705 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5706 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1),(4,6)], upper := (rows 35 194 28 73 400 33 66 164 292), lower := (rows 35 194 28 73 400 33 66 128 256), losses := [] }

theorem u5706 : Upper (D 7) (R 7) [34,192,24,65,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5707 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 194 28 73 400 33 68 162 290), lower := (rows 35 194 28 73 400 33 68 128 256), losses := [] }

theorem u5707 : Upper (D 7) (R 7) [34,192,24,65,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5707 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5708 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 28 73 400 33 96 134 262), lower := (rows 35 194 28 73 400 33 96 128 256), losses := [] }

theorem u5708 : Upper (D 7) (R 7) [34,192,24,65,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5709 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 28 76 274 33 65 160 416), lower := (rows 35 194 28 76 274 33 65 128 256), losses := [] }

theorem u5709 : Upper (D 7) (R 7) [34,192,24,68,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5710 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 28 76 274 33 96 129 385), lower := (rows 35 194 28 76 274 33 96 128 256), losses := [] }

theorem u5710 : Upper (D 7) (R 7) [34,192,24,68,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5710 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5711 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 76 274 33 192 161 289), lower := (rows 35 194 28 76 274 33 192 128 256), losses := [] }

theorem u5711 : Upper (D 7) (R 7) [34,192,24,68,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5712 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 400, targets := 1 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(4,0),(4,6)], upper := (rows 35 194 28 76 400 33 65 162 290), lower := (rows 35 194 28 76 400 33 65 128 256), losses := [] }

theorem u5712 : Upper (D 7) (R 7) [34,192,24,68,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5713 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 28 76 400 33 66 161 289), lower := (rows 35 194 28 76 400 33 66 128 256), losses := [] }

theorem u5713 : Upper (D 7) (R 7) [34,192,24,68,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5714 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(4,5),(4,6)], upper := (rows 35 194 28 76 400 33 96 131 259), lower := (rows 35 194 28 76 400 33 96 128 256), losses := [] }

theorem u5714 : Upper (D 7) (R 7) [34,192,24,68,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5714 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5715 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 406, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 28 104 400 33 65 134 262), lower := (rows 35 194 28 104 400 33 65 128 256), losses := [] }

theorem u5715 : Upper (D 7) (R 7) [34,192,24,96,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5715 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5716 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 41, targets := 128 },{ cop := 4, region := 66, targets := 33 }], pairs := [(0,7),(1,0),(1,5),(3,7)], upper := (rows 35 194 28 104 400 33 66 133 261), lower := (rows 35 194 28 104 400 33 66 128 256), losses := [] }

theorem u5716 : Upper (D 7) (R 7) [34,192,24,96,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5716 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5717 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(4,6)], upper := (rows 35 194 28 104 400 33 68 131 259), lower := (rows 35 194 28 104 400 33 68 128 256), losses := [] }

theorem u5717 : Upper (D 7) (R 7) [34,192,24,96,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5717 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5718 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 194 44 73 145 288 66 148 276), lower := (rows 35 194 44 73 145 288 66 128 256), losses := [] }

theorem u5718 : Upper (D 7) (R 7) [34,192,40,65,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5718 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5719 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7)], upper := (rows 35 194 44 73 145 288 68 146 274), lower := (rows 35 194 44 73 145 288 68 128 256), losses := [] }

theorem u5719 : Upper (D 7) (R 7) [34,192,40,65,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5719 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5720 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 44 73 145 288 80 134 262), lower := (rows 35 194 44 73 145 288 80 128 256), losses := [] }

theorem u5720 : Upper (D 7) (R 7) [34,192,40,65,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5720 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5721 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7),(3,1)], upper := (rows 35 194 44 73 148 288 65 146 274), lower := (rows 35 194 44 73 148 288 65 128 256), losses := [] }

theorem u5721 : Upper (D 7) (R 7) [34,192,40,65,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5721 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5722 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 194 44 73 148 288 66 145 273), lower := (rows 35 194 44 73 148 288 66 128 256), losses := [] }

theorem u5722 : Upper (D 7) (R 7) [34,192,40,65,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5722 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5723 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 44 73 148 288 80 131 259), lower := (rows 35 194 44 73 148 288 80 128 256), losses := [] }

theorem u5723 : Upper (D 7) (R 7) [34,192,40,65,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5723 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5724 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 194 44 73 273 48 66 132 388), lower := (rows 35 194 44 73 273 48 66 128 256), losses := [] }

theorem u5724 : Upper (D 7) (R 7) [34,192,40,65,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5724 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5725 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 76, targets := 130 }], pairs := [(2,1),(2,7)], upper := (rows 35 194 44 73 273 48 68 130 386), lower := (rows 35 194 44 73 273 48 68 128 256), losses := [] }

theorem u5725 : Upper (D 7) (R 7) [34,192,40,65,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5725 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5726 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 44 73 273 48 192 134 262), lower := (rows 35 194 44 73 273 48 192 128 256), losses := [] }

theorem u5726 : Upper (D 7) (R 7) [34,192,40,65,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5726 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5727 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 35 194 44 73 400 48 65 134 262), lower := (rows 35 194 44 73 400 48 65 128 256), losses := [] }

theorem u5727 : Upper (D 7) (R 7) [34,192,40,65,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5727 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5728 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 194 44 73 400 48 66 133 261), lower := (rows 35 194 44 73 400 48 66 128 256), losses := [] }

theorem u5728 : Upper (D 7) (R 7) [34,192,40,65,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5728 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5729 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 76, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 44 73 400 48 68 131 259), lower := (rows 35 194 44 73 400 48 68 128 256), losses := [] }

theorem u5729 : Upper (D 7) (R 7) [34,192,40,65,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5729 [(5,4),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5730 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 35 194 44 88 145 288 65 134 262), lower := (rows 35 194 44 88 145 288 65 128 256), losses := [] }

theorem u5730 : Upper (D 7) (R 7) [34,192,40,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5730 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5731 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 44 88 145 288 66 133 261), lower := (rows 35 194 44 88 145 288 66 128 256), losses := [] }

theorem u5731 : Upper (D 7) (R 7) [34,192,40,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5731 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5732 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(4,6)], upper := (rows 35 194 44 88 145 288 68 131 259), lower := (rows 35 194 44 88 145 288 68 128 256), losses := [] }

theorem u5732 : Upper (D 7) (R 7) [34,192,40,80,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5732 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5733 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(2,0)], upper := (rows 35 194 44 88 400 33 65 134 262), lower := (rows 35 194 44 88 400 33 65 128 256), losses := [{ target := 0, region := (rows 0 74 5 74 127 32 64 197 325), good := (rows 446 474 446 474 400 436 478 128 256) }] }

theorem u5733 : Upper (D 7) (R 7) [34,192,40,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5734 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 44 88 400 33 66 133 261), lower := (rows 35 194 44 88 400 33 66 128 256), losses := [] }

theorem u5734 : Upper (D 7) (R 7) [34,192,40,80,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5735 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 194 44 88 400 33 68 131 259), lower := (rows 35 194 44 88 400 33 68 128 256), losses := [] }

theorem u5735 : Upper (D 7) (R 7) [34,192,40,80,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5735 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5736 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 4, region := 66, targets := 33 }], pairs := [(0,6),(1,0),(1,5),(4,6)], upper := (rows 35 194 44 328 145 33 66 148 276), lower := (rows 35 194 44 328 145 33 66 128 256), losses := [] }

theorem u5736 : Upper (D 7) (R 7) [34,192,40,320,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5736 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5737 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 49, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,6),(4,5),(4,6)], upper := (rows 35 194 44 328 145 33 68 146 274), lower := (rows 35 194 44 328 145 33 68 128 256), losses := [] }

theorem u5737 : Upper (D 7) (R 7) [34,192,40,320,129,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5737 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5738 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 44 328 145 33 80 134 262), lower := (rows 35 194 44 328 145 33 80 128 256), losses := [] }

theorem u5738 : Upper (D 7) (R 7) [34,192,40,320,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5738 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5739 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(2,0)], upper := (rows 35 194 44 328 148 33 65 146 274), lower := (rows 35 194 44 328 148 33 65 128 256), losses := [{ target := 0, region := (rows 0 74 5 74 117 32 64 207 335), good := (rows 446 474 446 474 404 436 478 128 256) }] }

theorem u5739 : Upper (D 7) (R 7) [34,192,40,320,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5740 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 66, targets := 33 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 194 44 328 148 33 66 145 273), lower := (rows 35 194 44 328 148 33 66 128 256), losses := [] }

theorem u5740 : Upper (D 7) (R 7) [34,192,40,320,132,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5741 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 44 328 148 33 80 131 259), lower := (rows 35 194 44 328 148 33 80 128 256), losses := [] }

theorem u5741 : Upper (D 7) (R 7) [34,192,40,320,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5741 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5742 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 194 69 137 276 48 66 168 296), lower := (rows 35 194 69 137 276 48 66 128 256), losses := [] }

theorem u5742 : Upper (D 7) (R 7) [34,192,65,129,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5742 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5743 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 69 137 276 48 72 162 290), lower := (rows 35 194 69 137 276 48 72 128 256), losses := [] }

theorem u5743 : Upper (D 7) (R 7) [34,192,65,129,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5743 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5744 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 194 69 137 276 48 96 138 266), lower := (rows 35 194 69 137 276 48 96 128 256), losses := [] }

theorem u5744 : Upper (D 7) (R 7) [34,192,65,129,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5744 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5745 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 194 69 140 273 48 66 168 296), lower := (rows 35 194 69 140 273 48 66 128 256), losses := [] }

theorem u5745 : Upper (D 7) (R 7) [34,192,65,132,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5745 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5746 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 35 194 69 140 273 48 72 162 290), lower := (rows 35 194 69 140 273 48 72 128 256), losses := [] }

theorem u5746 : Upper (D 7) (R 7) [34,192,65,132,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5746 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5747 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 194 69 140 273 48 96 138 266), lower := (rows 35 194 69 140 273 48 96 128 256), losses := [] }

theorem u5747 : Upper (D 7) (R 7) [34,192,65,132,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5747 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5748 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 194 69 140 274 33 72 176 304), lower := (rows 35 194 69 140 274 33 72 128 256), losses := [] }

theorem u5748 : Upper (D 7) (R 7) [34,192,65,132,258,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5748 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5749 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 2, region := 168, targets := 2 }], pairs := [(0,7),(2,7),(3,1)], upper := (rows 35 194 69 140 274 33 80 168 296), lower := (rows 35 194 69 140 274 33 80 128 256), losses := [] }

theorem u5749 : Upper (D 7) (R 7) [34,192,65,132,258,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5749 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5750 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 69 140 274 33 96 152 280), lower := (rows 35 194 69 140 274 33 96 128 256), losses := [] }

theorem u5750 : Upper (D 7) (R 7) [34,192,65,132,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5751 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 35 194 69 140 280 33 66 176 304), lower := (rows 35 194 69 140 280 33 66 128 256), losses := [] }

theorem u5751 : Upper (D 7) (R 7) [34,192,65,132,264,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5752 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 37, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7)], upper := (rows 35 194 69 140 280 33 80 162 290), lower := (rows 35 194 69 140 280 33 80 128 256), losses := [] }

theorem u5752 : Upper (D 7) (R 7) [34,192,65,132,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5752 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5753 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 410, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 69 140 280 33 96 146 274), lower := (rows 35 194 69 140 280 33 96 128 256), losses := [] }

theorem u5753 : Upper (D 7) (R 7) [34,192,65,132,264,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5754 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1),(4,6)], upper := (rows 35 194 69 140 304 33 66 152 280), lower := (rows 35 194 69 140 304 33 66 128 256), losses := [] }

theorem u5754 : Upper (D 7) (R 7) [34,192,65,132,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5755 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 194 69 140 304 33 72 146 274), lower := (rows 35 194 69 140 304 33 72 128 256), losses := [] }

theorem u5755 : Upper (D 7) (R 7) [34,192,65,132,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5755 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5756 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 138, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 69 140 304 33 80 138 266), lower := (rows 35 194 69 140 304 33 80 128 256), losses := [] }

theorem u5756 : Upper (D 7) (R 7) [34,192,65,132,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5756 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5757 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 440, targets := 66 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 35 194 69 152 273 40 66 164 292), lower := (rows 35 194 69 152 273 40 66 128 256), losses := [] }

theorem u5757 : Upper (D 7) (R 7) [34,192,65,144,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5757 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5758 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 194 69 152 273 40 68 162 290), lower := (rows 35 194 69 152 273 40 68 128 256), losses := [] }

theorem u5758 : Upper (D 7) (R 7) [34,192,65,144,257,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5758 [(5,3),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5759 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 194 69 152 273 40 96 134 262), lower := (rows 35 194 69 152 273 40 96 128 256), losses := [] }

theorem u5759 : Upper (D 7) (R 7) [34,192,65,144,257,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5759 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5759
end Delivery.IrregularNine14.P07

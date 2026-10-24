import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0000

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 168 208 288 80 385 257), lower := (rows 35 14 69 168 208 288 80 128 256), losses := [] }

theorem u840 : Upper (D 9) (R 9) [34,12,65,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b840 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 144, targets := 256 }], pairs := [(2,5),(3,0),(4,0),(4,5),(4,8)], upper := (rows 35 14 69 168 208 288 320 145 273), lower := (rows 35 14 69 168 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 352 352 128 256), good := (rows 98 30 100 248 248 352 352 128 352) }] }

theorem u841 : Upper (D 9) (R 9) [34,12,65,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b841 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0),(2,5),(3,0),(4,5)], upper := (rows 35 14 69 168 273 288 80 192 448), lower := (rows 35 14 69 168 273 288 80 128 256), losses := [] }

theorem u842 : Upper (D 9) (R 9) [34,12,65,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b842 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8),(4,5)], upper := (rows 35 14 69 168 273 288 192 208 336), lower := (rows 35 14 69 168 273 288 192 128 256), losses := [] }

theorem u843 : Upper (D 9) (R 9) [34,12,65,160,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b843 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 69 168 336 288 65 144 400), lower := (rows 35 14 69 168 336 288 65 128 256), losses := [] }

theorem u844 : Upper (D 9) (R 9) [34,12,65,160,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b844 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b845 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,6),(1,6),(2,5),(3,6)], upper := (rows 35 14 69 168 336 288 80 129 385), lower := (rows 35 14 69 168 336 288 80 128 256), losses := [] }

theorem u845 : Upper (D 9) (R 9) [34,12,65,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b845 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b846 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8),(4,5)], upper := (rows 35 14 69 168 336 288 192 145 273), lower := (rows 35 14 69 168 336 288 192 128 256), losses := [] }

theorem u846 : Upper (D 9) (R 9) [34,12,65,160,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b846 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b847 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 69 168 400 288 65 208 336), lower := (rows 35 14 69 168 400 288 65 128 256), losses := [] }

theorem u847 : Upper (D 9) (R 9) [34,12,65,160,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b847 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b848 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 40, targets := 1 },{ cop := 4, region := 40, targets := 64 }], pairs := [(2,5),(3,0),(3,6),(4,5)], upper := (rows 35 14 69 168 400 288 80 193 321), lower := (rows 35 14 69 168 400 288 80 128 256), losses := [] }

theorem u848 : Upper (D 9) (R 9) [34,12,65,160,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b848 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b849 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 14 69 200 145 288 80 416 288), lower := (rows 35 14 69 200 145 288 80 128 256), losses := [] }

theorem u849 : Upper (D 9) (R 9) [34,12,65,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b849 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b850 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 14 69 200 145 288 96 400 272), lower := (rows 35 14 69 200 145 288 96 128 256), losses := [] }

theorem u850 : Upper (D 9) (R 9) [34,12,65,192,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b850 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b851 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 4, region := 360, targets := 1 },{ cop := 4, region := 356, targets := 128 }], pairs := [(0,6),(2,7),(3,0),(4,6),(4,8)], upper := (rows 35 14 69 200 145 288 320 176 304), lower := (rows 35 14 69 200 145 288 320 128 256), losses := [] }

theorem u851 : Upper (D 9) (R 9) [34,12,65,192,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b851 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 442, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(3,8)], upper := (rows 35 14 69 200 176 288 65 400 272), lower := (rows 35 14 69 200 176 288 65 128 256), losses := [] }

theorem u852 : Upper (D 9) (R 9) [34,12,65,192,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b852 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b853 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 69 200 176 288 80 385 257), lower := (rows 35 14 69 200 176 288 80 128 256), losses := [] }

theorem u853 : Upper (D 9) (R 9) [34,12,65,192,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b853 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b854 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,6),(3,0),(4,0),(4,6),(4,8)], upper := (rows 35 14 69 200 176 288 320 145 273), lower := (rows 35 14 69 200 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 24 352 352 128 256), good := (rows 98 30 100 248 248 352 352 128 352) }] }

theorem u854 : Upper (D 9) (R 9) [34,12,65,192,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b854 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b855 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 2, region := 426, targets := 1 }], pairs := [(0,6),(1,0),(3,0),(4,6)], upper := (rows 35 14 69 200 273 288 80 160 416), lower := (rows 35 14 69 200 273 288 80 128 256), losses := [] }

theorem u855 : Upper (D 9) (R 9) [34,12,65,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b855 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 14 69 200 273 288 96 144 400), lower := (rows 35 14 69 200 273 288 96 128 256), losses := [] }

theorem u856 : Upper (D 9) (R 9) [34,12,65,192,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b856 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b857 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 14 69 200 273 288 192 176 304), lower := (rows 35 14 69 200 273 288 192 128 256), losses := [] }

theorem u857 : Upper (D 9) (R 9) [34,12,65,192,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b857 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b858 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 69 200 400 48 65 416 288), lower := (rows 35 14 69 200 400 48 65 128 256), losses := [] }

theorem u858 : Upper (D 9) (R 9) [34,12,65,192,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b858 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b859 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 69 200 400 48 96 385 257), lower := (rows 35 14 69 200 400 48 96 128 256), losses := [] }

theorem u859 : Upper (D 9) (R 9) [34,12,65,192,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b859 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b860 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 324, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,6),(2,7),(3,0),(4,6)], upper := (rows 35 14 69 200 400 48 320 161 289), lower := (rows 35 14 69 200 400 48 320 128 256), losses := [] }

theorem u860 : Upper (D 9) (R 9) [34,12,65,192,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b860 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b861 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(3,0)], upper := (rows 35 14 69 200 400 288 65 176 304), lower := (rows 35 14 69 200 400 288 65 128 256), losses := [] }

theorem u861 : Upper (D 9) (R 9) [34,12,65,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b861 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b862 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(2,7)], upper := (rows 35 14 69 200 400 288 80 161 289), lower := (rows 35 14 69 200 400 288 80 128 256), losses := [] }

theorem u862 : Upper (D 9) (R 9) [34,12,65,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b862 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 14 69 200 400 288 96 145 273), lower := (rows 35 14 69 200 400 288 96 128 256), losses := [] }

theorem u863 : Upper (D 9) (R 9) [34,12,65,192,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b863 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b864 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 119, targets := 256 },{ cop := 2, region := 442, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 392 112 160 65 400 272), lower := (rows 35 14 69 392 112 160 65 128 256), losses := [] }

theorem u864 : Upper (D 9) (R 9) [34,12,65,384,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b864 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b865 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 392 112 160 80 385 257), lower := (rows 35 14 69 392 112 160 80 128 256), losses := [] }

theorem u865 : Upper (D 9) (R 9) [34,12,65,384,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b865 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b866 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 2, region := 176, targets := 256 },{ cop := 3, region := 112, targets := 1 }], pairs := [(0,6),(2,7),(4,0),(4,7),(4,8)], upper := (rows 35 14 69 392 112 160 320 145 273), lower := (rows 35 14 69 392 112 160 320 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 168 0 128 256), good := (rows 35 47 5 424 48 160 256 160 256) }] }

theorem u866 : Upper (D 9) (R 9) [34,12,65,384,96,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b866 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b867 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 392 145 48 96 448 320), lower := (rows 35 14 69 392 145 48 96 128 256), losses := [] }

theorem u867 : Upper (D 9) (R 9) [34,12,65,384,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b867 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b868 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 456, targets := 1 },{ cop := 0, region := 324, targets := 128 },{ cop := 2, region := 176, targets := 256 }], pairs := [(1,0),(2,7),(3,0),(4,8)], upper := (rows 35 14 69 392 145 48 320 224 352), lower := (rows 35 14 69 392 145 48 320 128 256), losses := [{ target := 0, region := (rows 0 6 4 61 16 48 381 177 305), good := (rows 490 78 462 456 504 504 320 128 320) }] }

theorem u868 : Upper (D 9) (R 9) [34,12,65,384,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b868 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b869 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 392 208 48 65 416 288), lower := (rows 35 14 69 392 208 48 65 128 256), losses := [] }

theorem u869 : Upper (D 9) (R 9) [34,12,65,384,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b869 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b870 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 392 208 48 96 385 257), lower := (rows 35 14 69 392 208 48 96 128 256), losses := [] }

theorem u870 : Upper (D 9) (R 9) [34,12,65,384,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b870 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b871 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 392, targets := 64 },{ cop := 0, region := 324, targets := 128 },{ cop := 2, region := 176, targets := 256 },{ cop := 3, region := 80, targets := 1 }], pairs := [(2,7),(3,6),(4,0),(4,8)], upper := (rows 35 14 69 392 208 48 320 161 289), lower := (rows 35 14 69 392 208 48 320 128 256), losses := [] }

theorem u871 : Upper (D 9) (R 9) [34,12,65,384,192,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b871 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 442, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(3,0),(4,0)], upper := (rows 35 14 69 392 208 288 65 176 304), lower := (rows 35 14 69 392 208 288 65 128 256), losses := [] }

theorem u872 : Upper (D 9) (R 9) [34,12,65,384,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b872 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b873 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 7, region := 80, targets := 1 }], pairs := [(0,6),(1,6),(3,6),(4,0)], upper := (rows 35 14 69 392 208 288 80 161 289), lower := (rows 35 14 69 392 208 288 80 128 256), losses := [] }

theorem u873 : Upper (D 9) (R 9) [34,12,65,384,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b873 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b874 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(1,5),(1,7),(3,5),(4,5)], upper := (rows 35 14 69 392 208 288 96 145 273), lower := (rows 35 14 69 392 208 288 96 128 256), losses := [] }

theorem u874 : Upper (D 9) (R 9) [34,12,65,384,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b874 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b875 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 72, targets := 384 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 14 84 104 145 288 65 384 384), lower := (rows 35 14 84 104 145 288 65 128 256), losses := [] }

theorem u875 : Upper (D 9) (R 9) [34,12,80,96,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b875 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b876 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,7),(1,7),(2,5),(3,7),(4,5)], upper := (rows 35 14 84 104 145 288 192 385 257), lower := (rows 35 14 84 104 145 288 192 128 256), losses := [] }

theorem u876 : Upper (D 9) (R 9) [34,12,80,96,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b876 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b877 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8),(4,8)], upper := (rows 35 14 84 104 145 288 320 129 385), lower := (rows 35 14 84 104 145 288 320 128 256), losses := [] }

theorem u877 : Upper (D 9) (R 9) [34,12,80,96,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b877 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b878 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8),(4,8)], upper := (rows 35 14 84 168 145 288 65 448 320), lower := (rows 35 14 84 168 145 288 65 128 256), losses := [] }

theorem u878 : Upper (D 9) (R 9) [34,12,80,160,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b878 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r879 : Route 9 := (fun mask => (mask,id))

def c879 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u879 : Upper (D 9) (R 9) [34,12,80,160,129,256,256] 13 := by
  apply FastRouting.sound _ _ [34,12,80,160,129,256,256] 13 (by decide) (choices 1) [1,64] r879 c879
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u41
  · exact u42

def b880 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8),(3,5)], upper := (rows 35 14 84 200 145 288 65 416 288), lower := (rows 35 14 84 200 145 288 65 128 256), losses := [] }

theorem u880 : Upper (D 9) (R 9) [34,12,80,192,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b880 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b881 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 400, targets := 32 },{ cop := 1, region := 289, targets := 128 },{ cop := 4, region := 356, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(4,5),(4,6)], upper := (rows 35 14 84 200 145 288 96 385 257), lower := (rows 35 14 84 200 145 288 96 128 256), losses := [] }

theorem u881 : Upper (D 9) (R 9) [34,12,80,192,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b881 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b882 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 1, region := 289, targets := 128 },{ cop := 4, region := 356, targets := 128 }], pairs := [(0,6),(0,7),(2,7),(4,6),(4,8)], upper := (rows 35 14 84 200 145 288 320 161 289), lower := (rows 35 14 84 200 145 288 320 128 256), losses := [] }

theorem u882 : Upper (D 9) (R 9) [34,12,80,192,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b882 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b883 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 84 200 176 288 65 385 257), lower := (rows 35 14 84 200 176 288 65 128 256), losses := [] }

theorem u883 : Upper (D 9) (R 9) [34,12,80,192,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b883 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b884 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 144, targets := 256 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(3,5),(4,6),(4,8)], upper := (rows 35 14 84 200 176 288 320 129 257), lower := (rows 35 14 84 200 176 288 320 128 256), losses := [] }

theorem u884 : Upper (D 9) (R 9) [34,12,80,192,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b884 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b885 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 84 200 400 33 65 416 288), lower := (rows 35 14 84 200 400 33 65 128 256), losses := [] }

theorem u885 : Upper (D 9) (R 9) [34,12,80,192,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b885 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b886 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 84 200 400 33 96 385 257), lower := (rows 35 14 84 200 400 33 96 128 256), losses := [] }

theorem u886 : Upper (D 9) (R 9) [34,12,80,192,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b886 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b887 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5),(3,0)], upper := (rows 35 14 84 200 400 33 320 161 289), lower := (rows 35 14 84 200 400 33 320 128 256), losses := [] }

theorem u887 : Upper (D 9) (R 9) [34,12,80,192,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b887 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b888 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 200, targets := 256 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(1,8),(3,8),(4,6)], upper := (rows 35 14 84 200 400 288 65 161 289), lower := (rows 35 14 84 200 400 288 65 128 256), losses := [{ target := 8, region := (rows 1 6 4 73 16 32 65 129 0), good := (rows 235 14 94 200 144 32 201 128 0) }] }

theorem u888 : Upper (D 9) (R 9) [34,12,80,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b888 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b889 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(3,0),(4,6)], upper := (rows 35 14 84 200 400 288 96 129 257), lower := (rows 35 14 84 200 400 288 96 128 256), losses := [] }

theorem u889 : Upper (D 9) (R 9) [34,12,80,192,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b889 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b890 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 68, targets := 384 },{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 14 100 200 400 288 65 145 273), lower := (rows 35 14 100 200 400 288 65 128 256), losses := [] }

theorem u890 : Upper (D 9) (R 9) [34,12,96,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b890 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b891 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8)], upper := (rows 35 14 100 200 400 288 80 129 257), lower := (rows 35 14 100 200 400 288 80 128 256), losses := [] }

theorem u891 : Upper (D 9) (R 9) [34,12,96,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b891 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b892 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 328, targets := 128 },{ cop := 4, region := 68, targets := 32 }], pairs := [(0,6),(2,5),(3,7),(4,6)], upper := (rows 35 14 196 328 145 48 65 416 288), lower := (rows 35 14 196 328 145 48 65 128 256), losses := [] }

theorem u892 : Upper (D 9) (R 9) [34,12,192,320,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b892 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b893 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 4, region := 100, targets := 257 }], pairs := [(0,6),(2,0),(2,8),(4,6)], upper := (rows 35 14 196 328 145 48 96 385 257), lower := (rows 35 14 196 328 145 48 96 128 256), losses := [] }

theorem u893 : Upper (D 9) (R 9) [34,12,192,320,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b893 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b894 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 183, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 196 328 145 48 320 161 289), lower := (rows 35 14 196 328 145 48 320 128 256), losses := [] }

theorem u894 : Upper (D 9) (R 9) [34,12,192,320,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b894 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b895 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(4,0),(4,6)], upper := (rows 35 14 196 328 176 33 65 400 272), lower := (rows 35 14 196 328 176 33 65 128 256), losses := [] }

theorem u895 : Upper (D 9) (R 9) [34,12,192,320,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b895 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b896 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 35 14 196 328 176 33 80 385 257), lower := (rows 35 14 196 328 176 33 80 128 256), losses := [] }

theorem u896 : Upper (D 9) (R 9) [34,12,192,320,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b896 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b897 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 183, targets := 256 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 14 196 328 176 33 320 145 273), lower := (rows 35 14 196 328 176 33 320 128 256), losses := [] }

theorem u897 : Upper (D 9) (R 9) [34,12,192,320,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b897 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b898 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 1, region := 33, targets := 384 },{ cop := 0, region := 400, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(4,0),(4,6)], upper := (rows 35 14 196 328 400 33 65 176 304), lower := (rows 35 14 196 328 400 33 65 128 256), losses := [] }

theorem u898 : Upper (D 9) (R 9) [34,12,192,320,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b898 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b899 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 14 196 328 400 33 80 161 289), lower := (rows 35 14 196 328 400 33 80 128 256), losses := [] }

theorem u899 : Upper (D 9) (R 9) [34,12,192,320,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b899 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u899
end Delivery.IrregularNine14.P09

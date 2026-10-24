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

def b780 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 7 196 328 400 40 80 161 289), lower := (rows 35 7 196 328 400 40 80 128 256), losses := [] }

theorem u780 : Upper (D 9) (R 9) [34,5,192,320,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b780 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b781 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 400, targets := 96 },{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0),(3,0),(4,5),(4,6)], upper := (rows 35 7 196 328 400 40 96 145 273), lower := (rows 35 7 196 328 400 40 96 128 256), losses := [] }

theorem u781 : Upper (D 9) (R 9) [34,5,192,320,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b781 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b782 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 458, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8),(3,8)], upper := (rows 35 14 21 73 176 288 192 448 320), lower := (rows 35 14 21 73 176 288 192 128 256), losses := [] }

theorem u782 : Upper (D 9) (R 9) [34,12,17,65,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b782 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b783 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 458, targets := 32 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,7),(1,5),(1,7),(3,5),(4,0)], upper := (rows 35 14 21 73 176 288 320 192 448), lower := (rows 35 14 21 73 176 288 320 128 256), losses := [{ target := 7, region := (rows 17 22 20 25 16 352 352 0 256), good := (rows 107 14 31 105 127 352 352 0 352) }] }

theorem u783 : Upper (D 9) (R 9) [34,12,17,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b783 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b784 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 14 21 73 208 288 96 384 384), lower := (rows 35 14 21 73 208 288 96 128 256), losses := [] }

theorem u784 : Upper (D 9) (R 9) [34,12,17,65,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b784 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b785 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,5)], upper := (rows 35 14 21 73 208 288 192 416 288), lower := (rows 35 14 21 73 208 288 192 128 256), losses := [] }

theorem u785 : Upper (D 9) (R 9) [34,12,17,65,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b785 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b786 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(0,7),(1,5),(3,5),(4,0)], upper := (rows 35 14 21 73 208 288 320 160 416), lower := (rows 35 14 21 73 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 6 4 9 16 0 352 128 256), good := (rows 75 14 31 73 208 320 320 128 320) },{ target := 7, region := (rows 17 22 20 25 16 352 352 0 256), good := (rows 107 14 31 105 127 352 352 0 352) }] }

theorem u786 : Upper (D 9) (R 9) [34,12,17,65,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b786 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b787 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 3, region := 406, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8),(3,8)], upper := (rows 35 14 21 73 400 160 96 448 320), lower := (rows 35 14 21 73 400 160 96 128 256), losses := [] }

theorem u787 : Upper (D 9) (R 9) [34,12,17,65,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b787 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b788 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 464, targets := 1 },{ cop := 0, region := 328, targets := 128 }], pairs := [(1,5),(1,7),(3,5),(3,7),(4,0)], upper := (rows 35 14 21 73 400 160 320 224 352), lower := (rows 35 14 21 73 400 160 320 128 256), losses := [{ target := 5, region := (rows 1 6 4 12 16 0 336 128 256), good := (rows 3 14 95 73 464 128 320 128 320) },{ target := 7, region := (rows 1 6 4 13 16 32 381 0 289), good := (rows 363 78 351 329 336 352 320 0 320) }] }

theorem u788 : Upper (D 9) (R 9) [34,12,17,65,384,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b788 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b789 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 72, targets := 384 },{ cop := 6, region := 424, targets := 1 }], pairs := [(2,5),(3,0),(3,7),(3,8),(4,5)], upper := (rows 35 14 21 104 208 288 65 384 384), lower := (rows 35 14 21 104 208 288 65 128 256), losses := [] }

theorem u789 : Upper (D 9) (R 9) [34,12,17,96,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b789 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b790 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 14 21 104 208 288 192 385 257), lower := (rows 35 14 21 104 208 288 192 128 256), losses := [] }

theorem u790 : Upper (D 9) (R 9) [34,12,17,96,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b790 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b791 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8),(4,8)], upper := (rows 35 14 21 104 208 288 320 129 385), lower := (rows 35 14 21 104 208 288 320 128 256), losses := [] }

theorem u791 : Upper (D 9) (R 9) [34,12,17,96,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b791 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b792 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 0, region := 468, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8),(3,8)], upper := (rows 35 14 21 104 400 160 65 448 320), lower := (rows 35 14 21 104 400 160 65 128 256), losses := [] }

theorem u792 : Upper (D 9) (R 9) [34,12,17,96,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b792 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b793 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 0, region := 328, targets := 128 },{ cop := 4, region := 104, targets := 1 }], pairs := [(1,0),(2,5),(3,0),(3,7),(4,5)], upper := (rows 35 14 21 104 400 160 320 193 321), lower := (rows 35 14 21 104 400 160 320 128 256), losses := [{ target := 0, region := (rows 0 6 4 28 16 176 336 128 256), good := (rows 34 14 126 104 504 160 320 160 320) }] }

theorem u793 : Upper (D 9) (R 9) [34,12,17,96,384,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b793 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b794 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 84, targets := 384 },{ cop := 2, region := 458, targets := 32 }], pairs := [(1,5),(2,7),(2,8),(4,7),(4,8)], upper := (rows 35 14 21 200 112 288 65 384 384), lower := (rows 35 14 21 200 112 288 65 128 256), losses := [] }

theorem u794 : Upper (D 9) (R 9) [34,12,17,192,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b794 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b795 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 14 21 200 112 288 192 385 257), lower := (rows 35 14 21 200 112 288 192 128 256), losses := [] }

theorem u795 : Upper (D 9) (R 9) [34,12,17,192,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b795 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b796 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 2, region := 458, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8),(3,8)], upper := (rows 35 14 21 200 112 288 320 129 385), lower := (rows 35 14 21 200 112 288 320 128 256), losses := [] }

theorem u796 : Upper (D 9) (R 9) [34,12,17,192,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b796 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b797 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 6, region := 440, targets := 1 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,7),(3,0),(4,0),(4,7)], upper := (rows 35 14 21 200 336 160 65 416 288), lower := (rows 35 14 21 200 336 160 65 128 256), losses := [] }

theorem u797 : Upper (D 9) (R 9) [34,12,17,192,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b797 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b798 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 340, targets := 128 },{ cop := 5, region := 72, targets := 257 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,7),(3,0),(3,8),(4,7)], upper := (rows 35 14 21 200 336 160 96 385 257), lower := (rows 35 14 21 200 336 160 96 128 256), losses := [] }

theorem u798 : Upper (D 9) (R 9) [34,12,17,192,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b798 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b799 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 14 21 200 336 160 320 161 289), lower := (rows 35 14 21 200 336 160 320 128 256), losses := [] }

theorem u799 : Upper (D 9) (R 9) [34,12,17,192,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b799 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b800 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 440, targets := 1 },{ cop := 0, region := 200, targets := 256 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(3,8),(4,0)], upper := (rows 35 14 21 200 336 288 65 160 416), lower := (rows 35 14 21 200 336 288 65 128 256), losses := [{ target := 0, region := (rows 0 6 4 88 88 511 64 511 511), good := (rows 418 446 446 504 504 416 504 416 416) }] }

theorem u800 : Upper (D 9) (R 9) [34,12,17,192,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b800 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b801 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 80, targets := 129 },{ cop := 0, region := 200, targets := 256 },{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6),(2,7),(3,8),(4,0),(4,7)], upper := (rows 35 14 21 200 336 288 96 129 385), lower := (rows 35 14 21 200 336 288 96 128 256), losses := [{ target := 7, region := (rows 1 2 5 8 304 304 373 0 256), good := (rows 119 78 117 72 368 368 112 0 368) }] }

theorem u801 : Upper (D 9) (R 9) [34,12,17,192,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b801 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b802 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 35 14 21 200 336 288 192 161 289), lower := (rows 35 14 21 200 336 288 192 128 256), losses := [] }

theorem u802 : Upper (D 9) (R 9) [34,12,17,192,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b802 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b803 : PairBound 9 := { available := 320, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 4, region := 356, targets := 1 },{ cop := 4, region := 72, targets := 256 }], pairs := [(1,5),(2,0),(3,5),(3,8),(4,5)], upper := (rows 35 14 52 73 145 288 192 448 320), lower := (rows 35 14 52 73 145 288 192 128 256), losses := [{ target := 5, region := (rows 1 6 4 25 25 0 511 511 511), good := (rows 475 478 478 473 473 448 448 448 448) }] }

theorem u803 : Upper (D 9) (R 9) [34,12,48,65,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b803 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b804 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 3, region := 144, targets := 256 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(3,5),(4,5),(4,8)], upper := (rows 35 14 52 73 145 288 320 192 448), lower := (rows 35 14 52 73 145 288 320 128 256), losses := [{ target := 5, region := (rows 1 6 4 25 25 0 511 511 511), good := (rows 475 478 478 473 473 448 448 448 448) }] }

theorem u804 : Upper (D 9) (R 9) [34,12,48,65,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b804 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b805 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 35 14 52 73 208 288 65 384 384), lower := (rows 35 14 52 73 208 288 65 128 256), losses := [] }

theorem u805 : Upper (D 9) (R 9) [34,12,48,65,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b805 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b806 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 303, targets := 128 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,7),(4,0)], upper := (rows 35 14 52 73 208 288 192 385 257), lower := (rows 35 14 52 73 208 288 192 128 256), losses := [] }

theorem u806 : Upper (D 9) (R 9) [34,12,48,65,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b806 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b807 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 417, targets := 64 },{ cop := 3, region := 144, targets := 256 }], pairs := [(0,6),(2,0),(3,5),(4,5),(4,8)], upper := (rows 35 14 52 73 208 288 320 129 385), lower := (rows 35 14 52 73 208 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 352 352 128 256), good := (rows 98 14 116 104 244 352 352 128 352) }] }

theorem u807 : Upper (D 9) (R 9) [34,12,48,65,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b807 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b808 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 14 69 88 145 288 96 384 384), lower := (rows 35 14 69 88 145 288 96 128 256), losses := [] }

theorem u808 : Upper (D 9) (R 9) [34,12,65,80,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b808 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b809 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8),(3,5)], upper := (rows 35 14 69 88 145 288 192 416 288), lower := (rows 35 14 69 88 145 288 192 128 256), losses := [] }

theorem u809 : Upper (D 9) (R 9) [34,12,65,80,129,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b809 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b810 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 144, targets := 256 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,6),(2,5),(3,0),(4,6),(4,8)], upper := (rows 35 14 69 88 145 288 320 160 416), lower := (rows 35 14 69 88 145 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 5 8 16 0 352 128 256), good := (rows 71 14 69 88 149 320 320 128 320) }] }

theorem u810 : Upper (D 9) (R 9) [34,12,65,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b810 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b811 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 79, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 35 14 69 88 176 288 65 384 384), lower := (rows 35 14 69 88 176 288 65 128 256), losses := [] }

theorem u811 : Upper (D 9) (R 9) [34,12,65,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b811 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b812 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 69 88 176 288 192 385 257), lower := (rows 35 14 69 88 176 288 192 128 256), losses := [] }

theorem u812 : Upper (D 9) (R 9) [34,12,65,80,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b812 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b813 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 433, targets := 64 },{ cop := 0, region := 452, targets := 32 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,6),(2,5),(3,0),(4,6),(4,8)], upper := (rows 35 14 69 88 176 288 320 129 385), lower := (rows 35 14 69 88 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 352 352 128 256), good := (rows 98 14 100 120 248 352 352 128 352) }] }

theorem u813 : Upper (D 9) (R 9) [34,12,65,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b813 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b814 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 84, targets := 384 }], pairs := [(2,7),(2,8),(4,7),(4,8)], upper := (rows 35 14 69 137 112 288 80 384 384), lower := (rows 35 14 69 137 112 288 80 128 256), losses := [] }

theorem u814 : Upper (D 9) (R 9) [34,12,65,129,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b814 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b815 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 70, targets := 288 },{ cop := 0, region := 464, targets := 1 }], pairs := [(1,5),(1,8),(2,5),(2,8),(4,0)], upper := (rows 35 14 69 137 112 288 192 400 272), lower := (rows 35 14 69 137 112 288 192 128 256), losses := [] }

theorem u815 : Upper (D 9) (R 9) [34,12,65,129,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b815 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b816 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 14 69 137 112 288 320 144 400), lower := (rows 35 14 69 137 112 288 320 128 256), losses := [] }

theorem u816 : Upper (D 9) (R 9) [34,12,65,129,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b816 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b817 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 86, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 14 69 137 208 288 80 416 288), lower := (rows 35 14 69 137 208 288 80 128 256), losses := [] }

theorem u817 : Upper (D 9) (R 9) [34,12,65,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b817 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b818 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 14 69 137 208 288 96 400 272), lower := (rows 35 14 69 137 208 288 96 128 256), losses := [] }

theorem u818 : Upper (D 9) (R 9) [34,12,65,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b818 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b819 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 464, targets := 1 }], pairs := [(1,5),(1,7),(2,5),(2,7),(4,0)], upper := (rows 35 14 69 137 208 288 320 176 304), lower := (rows 35 14 69 137 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 10 5 8 16 0 352 128 256), good := (rows 71 14 69 143 208 320 320 128 320) },{ target := 7, region := (rows 1 10 5 8 16 368 368 0 272), good := (rows 103 14 101 15 368 352 352 0 352) }] }

theorem u819 : Upper (D 9) (R 9) [34,12,65,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b819 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b820 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 14 69 137 336 48 96 384 384), lower := (rows 35 14 69 137 336 48 96 128 256), losses := [] }

theorem u820 : Upper (D 9) (R 9) [34,12,65,129,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b820 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b821 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 70, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 14 69 137 336 48 192 416 288), lower := (rows 35 14 69 137 336 48 192 128 256), losses := [] }

theorem u821 : Upper (D 9) (R 9) [34,12,65,129,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b821 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b822 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 14 69 137 336 48 320 160 416), lower := (rows 35 14 69 137 336 48 320 128 256), losses := [] }

theorem u822 : Upper (D 9) (R 9) [34,12,65,129,320,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b822 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b823 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 },{ cop := 0, region := 464, targets := 1 }], pairs := [(0,6),(1,6),(3,6),(4,0)], upper := (rows 35 14 69 137 336 288 80 160 416), lower := (rows 35 14 69 137 336 288 80 128 256), losses := [] }

theorem u823 : Upper (D 9) (R 9) [34,12,65,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b823 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b824 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 14 69 137 336 288 96 144 400), lower := (rows 35 14 69 137 336 288 96 128 256), losses := [] }

theorem u824 : Upper (D 9) (R 9) [34,12,65,129,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b824 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b825 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 288 },{ cop := 0, region := 464, targets := 1 }], pairs := [(1,5),(1,8),(2,5),(2,8),(4,0)], upper := (rows 35 14 69 137 336 288 192 176 304), lower := (rows 35 14 69 137 336 288 192 128 256), losses := [] }

theorem u825 : Upper (D 9) (R 9) [34,12,65,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b825 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b826 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 84, targets := 384 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,7),(2,8),(4,7),(4,8)], upper := (rows 35 14 69 152 112 288 65 384 384), lower := (rows 35 14 69 152 112 288 65 128 256), losses := [] }

theorem u826 : Upper (D 9) (R 9) [34,12,65,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b826 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r827 : Route 9 := (fun mask => (mask,id))

def c827 : Nat → Fin 9 := (fun mask => match mask with | 1 => 8 | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | _ => 0)

theorem u827 : Upper (D 9) (R 9) [34,12,65,144,96,256,128] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,96,256,128] 13 (by decide) (choices 1) [256] r827 c827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u38

def b828 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 14 69 152 112 288 320 129 385), lower := (rows 35 14 69 152 112 288 320 128 256), losses := [] }

theorem u828 : Upper (D 9) (R 9) [34,12,65,144,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b828 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b829 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 },{ cop := 0, region := 68, targets := 256 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 14 69 152 273 288 96 192 448), lower := (rows 35 14 69 152 273 288 96 128 256), losses := [] }

theorem u829 : Upper (D 9) (R 9) [34,12,65,144,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b829 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b830 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 196, targets := 256 },{ cop := 2, region := 304, targets := 128 },{ cop := 4, region := 232, targets := 1 }], pairs := [(0,7),(1,8),(2,8),(3,0),(4,7)], upper := (rows 35 14 69 152 273 288 192 224 352), lower := (rows 35 14 69 152 273 288 192 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 22 374 64 0 324), good := (rows 51 319 373 56 305 288 352 0 288) },{ target := 8, region := (rows 1 26 21 24 16 32 253 161 0), good := (rows 231 78 197 222 223 224 192 192 0) }] }

theorem u830 : Upper (D 9) (R 9) [34,12,65,144,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b830 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b831 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 442, targets := 1 },{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(1,0),(1,8),(3,0),(4,0)], upper := (rows 35 14 69 152 336 160 65 416 288), lower := (rows 35 14 69 152 336 160 65 128 256), losses := [] }

theorem u831 : Upper (D 9) (R 9) [34,12,65,144,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b831 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b832 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 3, region := 103, targets := 256 }], pairs := [(0,8),(1,5),(1,8),(3,5),(4,5)], upper := (rows 35 14 69 152 336 160 96 385 257), lower := (rows 35 14 69 152 336 160 96 128 256), losses := [] }

theorem u832 : Upper (D 9) (R 9) [34,12,65,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b832 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b833 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 14 69 152 336 160 320 161 289), lower := (rows 35 14 69 152 336 160 320 128 256), losses := [] }

theorem u833 : Upper (D 9) (R 9) [34,12,65,144,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b833 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b834 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 442, targets := 1 },{ cop := 6, region := 4, targets := 160 }], pairs := [(1,0),(2,5),(2,7),(3,0),(4,0)], upper := (rows 35 14 69 152 336 288 65 160 416), lower := (rows 35 14 69 152 336 288 65 128 256), losses := [] }

theorem u834 : Upper (D 9) (R 9) [34,12,65,144,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b834 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b835 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 5, region := 80, targets := 129 }], pairs := [(1,5),(3,5),(4,0),(4,5),(4,7)], upper := (rows 35 14 69 152 336 288 96 129 385), lower := (rows 35 14 69 152 336 288 96 128 256), losses := [] }

theorem u835 : Upper (D 9) (R 9) [34,12,65,144,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b835 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r836 : Route 9 := (fun mask => (mask,id))

def c836 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u836 : Upper (D 9) (R 9) [34,12,65,144,320,256,128] 13 := by
  apply FastRouting.sound _ _ [34,12,65,144,320,256,128] 13 (by decide) (choices 1) [1,32] r836 c836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u39
  · exact u40

def b837 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 168 145 288 80 448 320), lower := (rows 35 14 69 168 145 288 80 128 256), losses := [] }

theorem u837 : Upper (D 9) (R 9) [34,12,65,160,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b837 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b838 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 144, targets := 256 },{ cop := 4, region := 360, targets := 1 },{ cop := 4, region := 324, targets := 128 }], pairs := [(2,5),(2,7),(3,0),(4,5),(4,8)], upper := (rows 35 14 69 168 145 288 320 208 336), lower := (rows 35 14 69 168 145 288 320 128 256), losses := [] }

theorem u838 : Upper (D 9) (R 9) [34,12,65,160,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b838 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b839 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 87, targets := 256 },{ cop := 2, region := 442, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(4,8)], upper := (rows 35 14 69 168 208 288 65 400 272), lower := (rows 35 14 69 168 208 288 65 128 256), losses := [] }

theorem u839 : Upper (D 9) (R 9) [34,12,65,160,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b839 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u839
end Delivery.IrregularNine14.P09

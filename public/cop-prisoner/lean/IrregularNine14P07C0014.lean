import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0000

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b840 : PairBound 9 := { available := 8, camps := [{ cop := 1, region := 208, targets := 33 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(3,7),(4,0),(4,5)], upper := (rows 97 262 164 25 146 33 66 192 264), lower := (rows 97 262 164 25 146 33 66 192 256), losses := [] }

theorem u840 : Upper (D 7) (R 7) [96,260,160,17,130,1,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b841 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 81, targets := 2 },{ cop := 2, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 262 164 26 145 34 65 136 320), lower := (rows 97 262 164 26 145 34 65 136 256), losses := [] }

theorem u841 : Upper (D 7) (R 7) [96,260,160,18,129,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b841 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b842 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 302, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 164 26 145 34 65 192 264), lower := (rows 97 262 164 26 145 34 65 192 256), losses := [] }

theorem u842 : Upper (D 7) (R 7) [96,260,160,18,129,2,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b843 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 346, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 97 262 164 26 208 33 66 129 264), lower := (rows 97 262 164 26 208 33 66 129 256), losses := [] }

theorem u843 : Upper (D 7) (R 7) [96,260,160,18,192,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b844 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 216, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 97 262 164 26 208 33 66 136 257), lower := (rows 97 262 164 26 208 33 66 136 256), losses := [] }

theorem u844 : Upper (D 7) (R 7) [96,260,160,18,192,1,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b844 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b845 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 302, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 262 164 26 208 34 65 129 264), lower := (rows 97 262 164 26 208 34 65 129 256), losses := [] }

theorem u845 : Upper (D 7) (R 7) [96,260,160,18,192,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b846 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 81, targets := 2 },{ cop := 2, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 262 164 26 208 34 65 136 257), lower := (rows 97 262 164 26 208 34 65 136 256), losses := [] }

theorem u846 : Upper (D 7) (R 7) [96,260,160,18,192,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b846 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b847 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 97 290 7 25 146 36 192 136 320), lower := (rows 97 290 7 25 146 36 192 136 256), losses := [] }

theorem u847 : Upper (D 7) (R 7) [96,288,3,17,130,4,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b847 [(5,2),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b848 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 294, targets := 192 }], pairs := [(1,6),(1,7),(2,6)], upper := (rows 97 290 7 25 146 36 192 192 264), lower := (rows 97 290 7 25 146 36 192 192 256), losses := [] }

theorem u848 : Upper (D 7) (R 7) [96,288,3,17,130,4,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b848 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b849 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 97 290 7 26 145 36 192 136 320), lower := (rows 97 290 7 26 145 36 192 136 256), losses := [] }

theorem u849 : Upper (D 7) (R 7) [96,288,3,18,129,4,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b849 [(5,2),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b850 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 302, targets := 192 }], pairs := [(1,6),(1,7),(2,6)], upper := (rows 97 290 7 26 145 36 192 192 264), lower := (rows 97 290 7 26 145 36 192 192 256), losses := [] }

theorem u850 : Upper (D 7) (R 7) [96,288,3,18,129,4,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b850 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b851 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 366, targets := 1 },{ cop := 6, region := 161, targets := 2 }], pairs := [(0,1),(1,0),(2,0),(3,0)], upper := (rows 97 290 14 88 145 160 66 129 260), lower := (rows 97 290 14 88 145 160 66 129 256), losses := [] }

theorem u851 : Upper (D 7) (R 7) [96,288,10,80,129,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b851 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b852 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 323, targets := 128 },{ cop := 0, region := 258, targets := 64 }], pairs := [(0,7),(1,6),(1,7)], upper := (rows 97 290 14 88 145 160 66 132 257), lower := (rows 97 290 14 88 145 160 66 132 256), losses := [] }

theorem u852 : Upper (D 7) (R 7) [96,288,10,80,129,128,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b852 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b853 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 294, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 290 14 152 82 160 65 129 260), lower := (rows 97 290 14 152 82 160 65 129 256), losses := [] }

theorem u853 : Upper (D 7) (R 7) [96,288,10,144,66,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b853 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b854 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 140, targets := 65 }], pairs := [(2,0),(2,6),(3,0)], upper := (rows 97 290 14 152 82 160 65 132 257), lower := (rows 97 290 14 152 82 160 65 132 256), losses := [] }

theorem u854 : Upper (D 7) (R 7) [96,288,10,144,66,128,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b854 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b855 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 97 386 7 56 208 34 65 132 264), lower := (rows 97 386 7 56 208 34 65 132 256), losses := [] }

theorem u855 : Upper (D 7) (R 7) [96,384,3,48,192,2,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b855 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b856 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 217, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 97 386 7 56 208 34 65 136 260), lower := (rows 97 386 7 56 208 34 65 136 256), losses := [] }

theorem u856 : Upper (D 7) (R 7) [96,384,3,48,192,2,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b856 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b857 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 302, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(2,6)], upper := (rows 97 386 14 56 208 34 65 129 260), lower := (rows 97 386 14 56 208 34 65 129 256), losses := [] }

theorem u857 : Upper (D 7) (R 7) [96,384,10,48,192,2,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b857 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b858 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 65, targets := 130 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 386 14 56 208 34 65 132 257), lower := (rows 97 386 14 56 208 34 65 132 256), losses := [{ target := 1, region := (rows 41 0 4 8 148 32 109 132 365), good := (rows 353 400 477 377 464 353 321 468 256) }] }

theorem u858 : Upper (D 7) (R 7) [96,384,10,48,192,2,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b858 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b859 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 21 104 176 288 66 192 448), lower := (rows 7 11 21 104 176 288 66 128 256), losses := [] }

theorem u859 : Upper (D 7) (R 7) [6,9,17,96,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b859 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b860 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 4, region := 72, targets := 2 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 21 104 176 288 192 194 322), lower := (rows 7 11 21 104 176 288 192 128 256), losses := [] }

theorem u860 : Upper (D 7) (R 7) [6,9,17,96,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b860 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b861 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 21 104 304 160 66 192 448), lower := (rows 7 11 21 104 304 160 66 128 256), losses := [] }

theorem u861 : Upper (D 7) (R 7) [6,9,17,96,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b861 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b862 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 21 104 304 160 192 194 322), lower := (rows 7 11 21 104 304 160 192 128 256), losses := [] }

theorem u862 : Upper (D 7) (R 7) [6,9,17,96,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b862 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b863 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 472, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 21 104 400 34 192 224 352), lower := (rows 7 11 21 104 400 34 192 128 256), losses := [] }

theorem u863 : Upper (D 7) (R 7) [6,9,17,96,384,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b863 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b864 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6),(1,6),(2,6),(4,6)], upper := (rows 7 11 21 104 400 96 192 162 290), lower := (rows 7 11 21 104 400 96 192 128 256), losses := [] }

theorem u864 : Upper (D 7) (R 7) [6,9,17,96,384,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b864 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b865 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 21 296 112 160 66 192 448), lower := (rows 7 11 21 296 112 160 66 128 256), losses := [] }

theorem u865 : Upper (D 7) (R 7) [6,9,17,288,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b865 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b866 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 21 296 112 160 192 194 322), lower := (rows 7 11 21 296 112 160 192 128 256), losses := [] }

theorem u866 : Upper (D 7) (R 7) [6,9,17,288,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b866 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b867 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 21 296 208 96 66 160 416), lower := (rows 7 11 21 296 208 96 66 128 256), losses := [] }

theorem u867 : Upper (D 7) (R 7) [6,9,17,288,192,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b867 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b868 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 104, targets := 131 },{ cop := 7, region := 112, targets := 1 }], pairs := [(3,0),(3,1),(3,7),(4,0)], upper := (rows 7 11 21 296 208 96 96 130 386), lower := (rows 7 11 21 296 208 96 96 128 256), losses := [] }

theorem u868 : Upper (D 7) (R 7) [6,9,17,288,192,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b868 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b869 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 21 296 208 96 192 162 290), lower := (rows 7 11 21 296 208 96 192 128 256), losses := [] }

theorem u869 : Upper (D 7) (R 7) [6,9,17,288,192,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b869 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b870 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 37 88 176 288 66 192 448), lower := (rows 7 11 37 88 176 288 66 128 256), losses := [] }

theorem u870 : Upper (D 7) (R 7) [6,9,33,80,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b870 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b871 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 37 88 176 288 192 194 322), lower := (rows 7 11 37 88 176 288 192 128 256), losses := [] }

theorem u871 : Upper (D 7) (R 7) [6,9,33,80,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b871 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b872 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 37 88 304 160 66 192 448), lower := (rows 7 11 37 88 304 160 66 128 256), losses := [] }

theorem u872 : Upper (D 7) (R 7) [6,9,33,80,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b872 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b873 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(3,1),(3,5),(4,0)], upper := (rows 7 11 37 88 304 160 192 194 322), lower := (rows 7 11 37 88 304 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 224 224 128 256), good := (rows 5 9 101 120 376 224 224 224 256) },{ target := 5, region := (rows 1 2 4 24 16 0 231 131 259), good := (rows 455 459 453 88 344 192 192 192 256) }] }

theorem u873 : Upper (D 7) (R 7) [6,9,33,80,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b873 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b874 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 200 112 288 66 144 400), lower := (rows 7 11 37 200 112 288 66 128 256), losses := [] }

theorem u874 : Upper (D 7) (R 7) [6,9,33,192,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b874 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b875 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 37 200 112 288 80 130 386), lower := (rows 7 11 37 200 112 288 80 128 256), losses := [] }

theorem u875 : Upper (D 7) (R 7) [6,9,33,192,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b875 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b876 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 37 200 112 288 192 146 274), lower := (rows 7 11 37 200 112 288 192 128 256), losses := [] }

theorem u876 : Upper (D 7) (R 7) [6,9,33,192,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b876 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b877 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 200 336 48 66 160 416), lower := (rows 7 11 37 200 336 48 66 128 256), losses := [] }

theorem u877 : Upper (D 7) (R 7) [6,9,33,192,320,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b877 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b878 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 112, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 11 37 200 336 48 96 130 386), lower := (rows 7 11 37 200 336 48 96 128 256), losses := [] }

theorem u878 : Upper (D 7) (R 7) [6,9,33,192,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b878 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b879 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 37 200 336 48 192 162 290), lower := (rows 7 11 37 200 336 48 192 128 256), losses := [] }

theorem u879 : Upper (D 7) (R 7) [6,9,33,192,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b879 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b880 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 37 280 112 160 66 192 448), lower := (rows 7 11 37 280 112 160 66 128 256), losses := [] }

theorem u880 : Upper (D 7) (R 7) [6,9,33,272,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b880 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b881 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 37 280 112 160 192 194 322), lower := (rows 7 11 37 280 112 160 192 128 256), losses := [] }

theorem u881 : Upper (D 7) (R 7) [6,9,33,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b881 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b882 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 37 328 112 160 66 144 400), lower := (rows 7 11 37 328 112 160 66 128 256), losses := [] }

theorem u882 : Upper (D 7) (R 7) [6,9,33,320,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b882 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b883 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 80, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 11 37 328 112 160 80 130 386), lower := (rows 7 11 37 328 112 160 80 128 256), losses := [] }

theorem u883 : Upper (D 7) (R 7) [6,9,33,320,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b883 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b884 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 11 37 328 112 160 192 146 274), lower := (rows 7 11 37 328 112 160 192 128 256), losses := [] }

theorem u884 : Upper (D 7) (R 7) [6,9,33,320,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b884 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b885 : PairBound 9 := { available := 160, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 11 37 328 208 48 66 160 416), lower := (rows 7 11 37 328 208 48 66 128 256), losses := [] }

theorem u885 : Upper (D 7) (R 7) [6,9,33,320,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b885 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b886 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 7, region := 112, targets := 2 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 7 11 37 328 208 48 96 130 386), lower := (rows 7 11 37 328 208 48 96 128 256), losses := [] }

theorem u886 : Upper (D 7) (R 7) [6,9,33,320,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b886 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b887 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 37 328 208 48 192 162 290), lower := (rows 7 11 37 328 208 48 192 128 256), losses := [] }

theorem u887 : Upper (D 7) (R 7) [6,9,33,320,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b887 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b888 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 440, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 37 328 208 160 66 176 304), lower := (rows 7 11 37 328 208 160 66 128 256), losses := [] }

theorem u888 : Upper (D 7) (R 7) [6,9,33,320,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b888 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b889 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 11 37 328 208 160 80 162 290), lower := (rows 7 11 37 328 208 160 80 128 256), losses := [] }

theorem u889 : Upper (D 7) (R 7) [6,9,33,320,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b889 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r890 : Route 9 := (fun mask => (mask,id))

def c890 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u890 : Upper (D 7) (R 7) [6,9,33,320,192,128,32] 13 := by
  apply FastRouting.sound _ _ [6,9,33,320,192,128,32] 13 (by decide) (choices 1) [2,16] r890 c890
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u0
  · exact u1

def b891 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 11 52 104 208 288 65 130 386), lower := (rows 7 11 52 104 208 288 65 128 256), losses := [] }

theorem u891 : Upper (D 7) (R 7) [6,9,48,96,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b891 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b892 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 11 52 104 208 288 66 129 385), lower := (rows 7 11 52 104 208 288 66 128 256), losses := [] }

theorem u892 : Upper (D 7) (R 7) [6,9,48,96,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b892 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b893 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 52 104 208 288 192 131 259), lower := (rows 7 11 52 104 208 288 192 128 256), losses := [] }

theorem u893 : Upper (D 7) (R 7) [6,9,48,96,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b893 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b894 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 6, region := 168, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(3,7)], upper := (rows 7 11 52 104 273 160 66 192 448), lower := (rows 7 11 52 104 273 160 66 128 256), losses := [] }

theorem u894 : Upper (D 7) (R 7) [6,9,48,96,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b894 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b895 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 104 273 160 192 194 322), lower := (rows 7 11 52 104 273 160 192 128 256), losses := [] }

theorem u895 : Upper (D 7) (R 7) [6,9,48,96,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b895 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b896 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 6, region := 168, targets := 1 }], pairs := [(0,7),(1,7),(3,0),(3,7)], upper := (rows 7 11 52 104 274 160 65 192 448), lower := (rows 7 11 52 104 274 160 65 128 256), losses := [] }

theorem u896 : Upper (D 7) (R 7) [6,9,48,96,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b896 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b897 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 11 52 104 274 160 192 193 321), lower := (rows 7 11 52 104 274 160 192 128 256), losses := [] }

theorem u897 : Upper (D 7) (R 7) [6,9,48,96,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b897 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b898 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(3,7),(4,5)], upper := (rows 7 11 52 104 336 160 65 130 386), lower := (rows 7 11 52 104 336 160 65 128 256), losses := [] }

theorem u898 : Upper (D 7) (R 7) [6,9,48,96,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b898 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b899 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 75, targets := 128 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,7),(1,7),(3,7),(4,5)], upper := (rows 7 11 52 104 336 160 66 129 385), lower := (rows 7 11 52 104 336 160 66 128 256), losses := [] }

theorem u899 : Upper (D 7) (R 7) [6,9,48,96,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b899 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u899
end Delivery.IrregularNine14.P07

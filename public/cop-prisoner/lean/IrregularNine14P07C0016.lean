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

def b960 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 100 296 82 160 80 129 385), lower := (rows 7 11 100 296 82 160 80 128 256), losses := [] }

theorem u960 : Upper (D 7) (R 7) [6,9,96,288,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b960 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b961 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 11 100 296 82 160 192 145 273), lower := (rows 7 11 100 296 82 160 192 128 256), losses := [] }

theorem u961 : Upper (D 7) (R 7) [6,9,96,288,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b961 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b962 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 7 11 100 296 145 160 66 208 336), lower := (rows 7 11 100 296 145 160 66 128 256), losses := [] }

theorem u962 : Upper (D 7) (R 7) [6,9,96,288,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b962 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b963 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 11 100 296 145 160 80 194 322), lower := (rows 7 11 100 296 145 160 80 128 256), losses := [] }

theorem u963 : Upper (D 7) (R 7) [6,9,96,288,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b963 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b964 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 0, region := 208, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(4,5)], upper := (rows 7 11 100 296 146 160 65 208 336), lower := (rows 7 11 100 296 146 160 65 128 256), losses := [] }

theorem u964 : Upper (D 7) (R 7) [6,9,96,288,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b964 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b965 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 11 100 296 146 160 80 193 321), lower := (rows 7 11 100 296 146 160 80 128 256), losses := [] }

theorem u965 : Upper (D 7) (R 7) [6,9,96,288,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b965 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b966 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 7 11 100 296 208 160 65 146 274), lower := (rows 7 11 100 296 208 160 65 128 256), losses := [] }

theorem u966 : Upper (D 7) (R 7) [6,9,96,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b966 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b967 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 },{ cop := 4, region := 36, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 7 11 100 296 208 160 66 145 273), lower := (rows 7 11 100 296 208 160 66 128 256), losses := [] }

theorem u967 : Upper (D 7) (R 7) [6,9,96,288,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b967 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b968 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 84, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 100 296 208 160 80 131 259), lower := (rows 7 11 100 296 208 160 80 128 256), losses := [] }

theorem u968 : Upper (D 7) (R 7) [6,9,96,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b968 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b969 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 392, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 7 11 100 392 145 34 80 224 352), lower := (rows 7 11 100 392 145 34 80 128 256), losses := [{ target := 0, region := (rows 0 2 20 93 16 35 80 148 276), good := (rows 430 42 492 392 508 34 476 128 256) }] }

theorem u969 : Upper (D 7) (R 7) [6,9,96,384,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b969 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b970 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5),(4,5)], upper := (rows 7 11 100 392 145 34 96 208 336), lower := (rows 7 11 100 392 145 34 96 128 256), losses := [] }

theorem u970 : Upper (D 7) (R 7) [6,9,96,384,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b970 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b971 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 100 392 145 48 96 194 322), lower := (rows 7 11 100 392 145 48 96 128 256), losses := [] }

theorem u971 : Upper (D 7) (R 7) [6,9,96,384,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b971 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b972 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 392, targets := 3 },{ cop := 4, region := 101, targets := 128 }], pairs := [(0,7),(3,0),(3,1)], upper := (rows 7 11 100 392 146 33 80 224 352), lower := (rows 7 11 100 392 146 33 80 128 256), losses := [] }

theorem u972 : Upper (D 7) (R 7) [6,9,96,384,130,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b972 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b973 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 100 392 146 48 96 193 321), lower := (rows 7 11 100 392 146 48 96 128 256), losses := [] }

theorem u973 : Upper (D 7) (R 7) [6,9,96,384,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b973 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b974 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 100 392 176 33 66 208 336), lower := (rows 7 11 100 392 176 33 66 128 256), losses := [] }

theorem u974 : Upper (D 7) (R 7) [6,9,96,384,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b974 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b975 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 100 392 176 33 80 194 322), lower := (rows 7 11 100 392 176 33 80 128 256), losses := [] }

theorem u975 : Upper (D 7) (R 7) [6,9,96,384,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b975 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b976 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 100 392 176 34 65 208 336), lower := (rows 7 11 100 392 176 34 65 128 256), losses := [] }

theorem u976 : Upper (D 7) (R 7) [6,9,96,384,160,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b976 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b977 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 100 392 176 34 80 193 321), lower := (rows 7 11 100 392 176 34 80 128 256), losses := [] }

theorem u977 : Upper (D 7) (R 7) [6,9,96,384,160,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b977 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b978 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 37 73 304 160 66 192 448), lower := (rows 7 26 37 73 304 160 66 128 256), losses := [] }

theorem u978 : Upper (D 7) (R 7) [6,24,33,65,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b978 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b979 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(2,1),(3,5),(4,0)], upper := (rows 7 26 37 73 304 160 192 194 322), lower := (rows 7 26 37 73 304 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 12 12 16 224 224 128 256), good := (rows 13 28 109 109 368 224 224 224 256) }] }

theorem u979 : Upper (D 7) (R 7) [6,24,33,65,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b979 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b980 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 26 37 74 304 160 65 192 448), lower := (rows 7 26 37 74 304 160 65 128 256), losses := [] }

theorem u980 : Upper (D 7) (R 7) [6,24,33,66,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b980 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b981 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(2,1),(3,5),(4,1)], upper := (rows 7 26 37 74 304 160 192 193 321), lower := (rows 7 26 37 74 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 224 224 128 256), good := (rows 6 26 100 106 378 224 224 224 256) }] }

theorem u981 : Upper (D 7) (R 7) [6,24,33,66,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b981 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b982 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 6, region := 168, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,5)], upper := (rows 7 26 37 104 273 160 66 192 448), lower := (rows 7 26 37 104 273 160 66 128 256), losses := [] }

theorem u982 : Upper (D 7) (R 7) [6,24,33,96,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b982 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b983 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 26 37 104 273 160 192 194 322), lower := (rows 7 26 37 104 273 160 192 128 256), losses := [] }

theorem u983 : Upper (D 7) (R 7) [6,24,33,96,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b983 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b984 : PairBound 9 := { available := 192, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 228, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 26 37 104 274 160 65 192 448), lower := (rows 7 26 37 104 274 160 65 128 256), losses := [] }

theorem u984 : Upper (D 7) (R 7) [6,24,33,96,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b984 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b985 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 26 37 104 274 160 192 193 321), lower := (rows 7 26 37 104 274 160 192 128 256), losses := [] }

theorem u985 : Upper (D 7) (R 7) [6,24,33,96,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b985 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b986 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 7 26 37 104 336 160 65 130 386), lower := (rows 7 26 37 104 336 160 65 128 256), losses := [] }

theorem u986 : Upper (D 7) (R 7) [6,24,33,96,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b986 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b987 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 0, region := 464, targets := 32 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,1),(2,6),(4,5)], upper := (rows 7 26 37 104 336 160 66 129 385), lower := (rows 7 26 37 104 336 160 66 128 256), losses := [] }

theorem u987 : Upper (D 7) (R 7) [6,24,33,96,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b987 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b988 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 26 37 104 336 160 192 131 259), lower := (rows 7 26 37 104 336 160 192 128 256), losses := [] }

theorem u988 : Upper (D 7) (R 7) [6,24,33,96,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b988 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b989 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 7 26 37 200 336 160 65 162 290), lower := (rows 7 26 37 200 336 160 65 128 256), losses := [] }

theorem u989 : Upper (D 7) (R 7) [6,24,33,192,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b989 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b990 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 164, targets := 66 },{ cop := 1, region := 165, targets := 64 }], pairs := [(0,6),(2,1),(2,6),(4,7)], upper := (rows 7 26 37 200 336 160 66 161 289), lower := (rows 7 26 37 200 336 160 66 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 21 32 67 0 260), good := (rows 343 90 373 72 336 32 66 0 256) }] }

theorem u990 : Upper (D 7) (R 7) [6,24,33,192,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b990 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b991 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 5, region := 72, targets := 3 }], pairs := [(0,6),(2,6),(3,0),(3,1)], upper := (rows 7 26 37 200 336 160 96 131 259), lower := (rows 7 26 37 200 336 160 96 128 256), losses := [] }

theorem u991 : Upper (D 7) (R 7) [6,24,33,192,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b991 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b992 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 466, targets := 32 },{ cop := 6, region := 164, targets := 3 }], pairs := [(1,5),(2,0),(2,1),(4,5)], upper := (rows 7 26 100 41 273 160 66 192 448), lower := (rows 7 26 100 41 273 160 66 128 256), losses := [] }

theorem u992 : Upper (D 7) (R 7) [6,24,96,33,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b992 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b993 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 26 100 41 273 160 192 194 322), lower := (rows 7 26 100 41 273 160 192 128 256), losses := [] }

theorem u993 : Upper (D 7) (R 7) [6,24,96,33,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b993 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b994 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 68, targets := 130 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(2,1),(2,7),(4,5)], upper := (rows 7 26 100 41 336 160 65 130 386), lower := (rows 7 26 100 41 336 160 65 128 256), losses := [] }

theorem u994 : Upper (D 7) (R 7) [6,24,96,33,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b994 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b995 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 168, targets := 66 },{ cop := 3, region := 466, targets := 32 }], pairs := [(1,5),(3,1),(3,6),(4,5)], upper := (rows 7 26 100 41 336 160 66 129 385), lower := (rows 7 26 100 41 336 160 66 128 256), losses := [] }

theorem u995 : Upper (D 7) (R 7) [6,24,96,33,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b995 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b996 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 26 100 41 336 160 192 131 259), lower := (rows 7 26 100 41 336 160 192 128 256), losses := [] }

theorem u996 : Upper (D 7) (R 7) [6,24,96,33,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b996 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b997 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 69, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 26 100 42 273 160 65 192 448), lower := (rows 7 26 100 42 273 160 65 128 256), losses := [] }

theorem u997 : Upper (D 7) (R 7) [6,24,96,34,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b997 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b998 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 26 100 42 273 160 192 193 321), lower := (rows 7 26 100 42 273 160 192 128 256), losses := [] }

theorem u998 : Upper (D 7) (R 7) [6,24,96,34,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b998 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b999 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 196, targets := 3 }], pairs := [(2,0),(2,1),(3,1),(4,1)], upper := (rows 7 26 100 137 273 34 192 224 352), lower := (rows 7 26 100 137 273 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 36 9 17 32 237 164 292), good := (rows 477 88 484 217 345 484 192 192 256) }] }

theorem u999 : Upper (D 7) (R 7) [6,24,96,129,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b999 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1000 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 137 273 96 192 162 290), lower := (rows 7 26 100 137 273 96 192 128 256), losses := [] }

theorem u1000 : Upper (D 7) (R 7) [6,24,96,129,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1000 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1001 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 5, region := 196, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(3,1)], upper := (rows 7 26 100 137 274 33 192 224 352), lower := (rows 7 26 100 137 274 33 192 128 256), losses := [{ target := 0, region := (rows 0 10 36 8 17 32 237 164 292), good := (rows 470 90 484 218 274 500 192 192 256) }] }

theorem u1001 : Upper (D 7) (R 7) [6,24,96,129,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1001 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1002 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 137 274 96 192 161 289), lower := (rows 7 26 100 137 274 96 192 128 256), losses := [] }

theorem u1002 : Upper (D 7) (R 7) [6,24,96,129,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1002 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1003 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(3,1),(3,5)], upper := (rows 7 26 100 137 304 34 65 192 448), lower := (rows 7 26 100 137 304 34 65 128 256), losses := [] }

theorem u1003 : Upper (D 7) (R 7) [6,24,96,129,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1003 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1004 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 200, targets := 34 }], pairs := [(2,0),(2,1),(3,1),(3,5)], upper := (rows 7 26 100 137 304 34 192 193 321), lower := (rows 7 26 100 137 304 34 192 128 256), losses := [{ target := 0, region := (rows 0 2 14 8 16 35 200 128 256), good := (rows 38 126 100 236 304 38 192 192 256) },{ target := 1, region := (rows 1 0 36 9 16 32 203 137 265), good := (rows 461 472 100 457 308 100 192 192 256) }] }

theorem u1004 : Upper (D 7) (R 7) [6,24,96,129,288,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1004 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1005 : Route 9 := (fun mask => (mask,id))

def c1005 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1005 : Upper (D 7) (R 7) [6,24,96,129,288,128,1] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,128,1] 13 (by decide) (choices 1) [2,64] r1005 c1005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u12
  · exact u13

def r1006 : Route 9 := (fun mask => (mask,id))

def c1006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1006 : Upper (D 7) (R 7) [6,24,96,129,288,128,2] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288,128,2] 13 (by decide) (choices 1) [1,64] r1006 c1006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u14
  · exact u15

def b1007 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 101, targets := 128 },{ cop := 2, region := 400, targets := 3 }], pairs := [(0,7),(2,7),(4,0),(4,1)], upper := (rows 7 26 100 137 400 33 66 224 352), lower := (rows 7 26 100 137 400 33 66 128 256), losses := [] }

theorem u1007 : Upper (D 7) (R 7) [6,24,96,129,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1007 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1008 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5),(4,5)], upper := (rows 7 26 100 137 400 33 96 194 322), lower := (rows 7 26 100 137 400 33 96 128 256), losses := [] }

theorem u1008 : Upper (D 7) (R 7) [6,24,96,129,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1008 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1009 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5),(4,5)], upper := (rows 7 26 100 137 400 34 96 193 321), lower := (rows 7 26 100 137 400 34 96 128 256), losses := [] }

theorem u1009 : Upper (D 7) (R 7) [6,24,96,129,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1009 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1010 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 196, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(4,1)], upper := (rows 7 26 100 138 273 33 192 224 352), lower := (rows 7 26 100 138 273 33 192 128 256), losses := [{ target := 0, region := (rows 0 18 36 9 16 32 237 164 292), good := (rows 462 90 484 202 346 492 192 192 256) }] }

theorem u1010 : Upper (D 7) (R 7) [6,24,96,130,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1010 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1011 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6),(1,6),(3,6),(4,6)], upper := (rows 7 26 100 138 273 96 192 161 289), lower := (rows 7 26 100 138 273 96 192 128 256), losses := [] }

theorem u1011 : Upper (D 7) (R 7) [6,24,96,130,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1011 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1012 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,7)], upper := (rows 7 26 100 138 304 160 65 193 321), lower := (rows 7 26 100 138 304 160 65 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 20 32 65 0 321), good := (rows 343 26 372 10 304 32 321 0 256) }] }

theorem u1012 : Upper (D 7) (R 7) [6,24,96,130,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1012 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1013 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,5)], upper := (rows 7 26 100 168 273 34 65 192 448), lower := (rows 7 26 100 168 273 34 65 128 256), losses := [] }

theorem u1013 : Upper (D 7) (R 7) [6,24,96,160,257,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1013 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1014 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(4,1),(4,5)], upper := (rows 7 26 100 168 273 34 192 193 321), lower := (rows 7 26 100 168 273 34 192 128 256), losses := [] }

theorem u1014 : Upper (D 7) (R 7) [6,24,96,160,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1014 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1015 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(3,0),(4,0)], upper := (rows 7 26 100 168 336 33 65 130 386), lower := (rows 7 26 100 168 336 33 65 128 256), losses := [] }

theorem u1015 : Upper (D 7) (R 7) [6,24,96,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1015 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1016 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 168, targets := 66 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(3,1),(3,6)], upper := (rows 7 26 100 168 336 33 66 129 385), lower := (rows 7 26 100 168 336 33 66 128 256), losses := [] }

theorem u1016 : Upper (D 7) (R 7) [6,24,96,160,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1016 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1017 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 68, targets := 3 },{ cop := 0, region := 464, targets := 32 },{ cop := 0, region := 168, targets := 64 }], pairs := [(2,0),(2,1),(3,6),(4,5)], upper := (rows 7 26 100 168 336 33 192 131 259), lower := (rows 7 26 100 168 336 33 192 128 256), losses := [] }

theorem u1017 : Upper (D 7) (R 7) [6,24,96,160,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1017 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1018 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7),(2,7),(4,1),(4,5)], upper := (rows 7 26 100 168 336 34 65 129 385), lower := (rows 7 26 100 168 336 34 65 128 256), losses := [] }

theorem u1018 : Upper (D 7) (R 7) [6,24,96,160,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1018 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1019 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 464, targets := 34 },{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(4,1),(4,5)], upper := (rows 7 26 100 168 336 34 192 129 257), lower := (rows 7 26 100 168 336 34 192 128 256), losses := [] }

theorem u1019 : Upper (D 7) (R 7) [6,24,96,160,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1019 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1019
end Delivery.IrregularNine14.P07

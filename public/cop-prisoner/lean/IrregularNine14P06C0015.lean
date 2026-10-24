import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0000

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b900 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 11 164 328 81 48 68 162 290), lower := (rows 7 11 164 328 81 48 68 128 256), losses := [] }

theorem u900 : Upper (D 6) (R 6) [6,9,160,320,65,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b900 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b901 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 112, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 11 164 328 81 48 96 134 262), lower := (rows 7 11 164 328 81 48 96 128 256), losses := [] }

theorem u901 : Upper (D 6) (R 6) [6,9,160,320,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b901 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b902 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(2,0),(4,0),(4,5)], upper := (rows 7 11 164 328 84 33 66 176 304), lower := (rows 7 11 164 328 84 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 57 49 32 67 164 292), good := (rows 478 90 444 328 476 508 66 128 256) }] }

theorem u902 : Upper (D 6) (R 6) [6,9,160,320,68,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b902 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b903 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 164 328 84 33 80 162 290), lower := (rows 7 11 164 328 84 33 80 128 256), losses := [] }

theorem u903 : Upper (D 6) (R 6) [6,9,160,320,68,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b903 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b904 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 267, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 328 84 33 96 146 274), lower := (rows 7 11 164 328 84 33 96 128 256), losses := [] }

theorem u904 : Upper (D 6) (R 6) [6,9,160,320,68,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b904 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b905 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 80, targets := 34 }], pairs := [(2,0),(4,1),(4,5)], upper := (rows 7 11 164 328 84 34 65 176 304), lower := (rows 7 11 164 328 84 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 103 88 88 35 64 194 322), good := (rows 422 446 164 476 476 422 508 128 256) }] }

theorem u905 : Upper (D 6) (R 6) [6,9,160,320,68,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b905 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b906 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 11 164 328 84 34 80 161 289), lower := (rows 7 11 164 328 84 34 80 128 256), losses := [] }

theorem u906 : Upper (D 6) (R 6) [6,9,160,320,68,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b906 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b907 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 267, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 11 164 328 84 34 96 145 273), lower := (rows 7 11 164 328 84 34 96 128 256), losses := [] }

theorem u907 : Upper (D 6) (R 6) [6,9,160,320,68,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b907 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b908 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,1),(4,5)], upper := (rows 7 11 164 328 84 48 65 162 290), lower := (rows 7 11 164 328 84 48 65 128 256), losses := [] }

theorem u908 : Upper (D 6) (R 6) [6,9,160,320,68,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b908 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b909 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 80, targets := 1 },{ cop := 0, region := 80, targets := 32 }], pairs := [(4,0),(4,5)], upper := (rows 7 11 164 328 84 48 66 161 289), lower := (rows 7 11 164 328 84 48 66 128 256), losses := [] }

theorem u909 : Upper (D 6) (R 6) [6,9,160,320,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b909 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b910 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 116, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 164 328 84 48 96 131 259), lower := (rows 7 11 164 328 84 48 96 128 256), losses := [] }

theorem u910 : Upper (D 6) (R 6) [6,9,160,320,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b910 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b911 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 328 112 33 66 148 276), lower := (rows 7 11 164 328 112 33 66 128 256), losses := [] }

theorem u911 : Upper (D 6) (R 6) [6,9,160,320,96,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b911 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b912 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(2,0),(4,0),(4,1)], upper := (rows 7 11 164 328 112 33 68 146 274), lower := (rows 7 11 164 328 112 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 36 43 52 32 117 129 257), good := (rows 478 458 252 328 124 508 84 128 256) }] }

theorem u912 : Upper (D 6) (R 6) [6,9,160,320,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b912 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b913 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 328 112 33 80 134 262), lower := (rows 7 11 164 328 112 33 80 128 256), losses := [] }

theorem u913 : Upper (D 6) (R 6) [6,9,160,320,96,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b913 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b914 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 164 328 112 34 65 148 276), lower := (rows 7 11 164 328 112 34 65 128 256), losses := [] }

theorem u914 : Upper (D 6) (R 6) [6,9,160,320,96,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b914 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b915 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(3,1),(4,0),(4,1)], upper := (rows 7 11 164 328 112 34 68 145 273), lower := (rows 7 11 164 328 112 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 11 20 32 69 129 257), good := (rows 477 457 244 328 112 40 84 128 256) }] }

theorem u915 : Upper (D 6) (R 6) [6,9,160,320,96,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b915 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b916 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 164 328 112 34 80 133 261), lower := (rows 7 11 164 328 112 34 80 128 256), losses := [] }

theorem u916 : Upper (D 6) (R 6) [6,9,160,320,96,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b916 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b917 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 388 26 112 33 68 224 352), lower := (rows 7 11 388 26 112 33 68 128 256), losses := [] }

theorem u917 : Upper (D 6) (R 6) [6,9,384,18,96,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b917 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b918 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 11 388 26 112 36 96 193 321), lower := (rows 7 11 388 26 112 36 96 128 256), losses := [] }

theorem u918 : Upper (D 6) (R 6) [6,9,384,18,96,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b918 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b919 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 388 42 84 96 65 176 304), lower := (rows 7 11 388 42 84 96 65 128 256), losses := [] }

theorem u919 : Upper (D 6) (R 6) [6,9,384,34,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b919 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b920 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 11 388 42 84 96 80 161 289), lower := (rows 7 11 388 42 84 96 80 128 256), losses := [] }

theorem u920 : Upper (D 6) (R 6) [6,9,384,34,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b920 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b921 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 120, targets := 1 },{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 7 11 388 42 84 96 96 145 273), lower := (rows 7 11 388 42 84 96 96 128 256), losses := [] }

theorem u921 : Upper (D 6) (R 6) [6,9,384,34,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b921 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b922 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 428, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 11 388 56 82 36 65 224 352), lower := (rows 7 11 388 56 82 36 65 128 256), losses := [] }

theorem u922 : Upper (D 6) (R 6) [6,9,384,48,66,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b922 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b923 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 120, targets := 1 },{ cop := 4, region := 389, targets := 32 }], pairs := [(0,5),(3,0),(4,0)], upper := (rows 7 11 388 56 82 36 96 193 321), lower := (rows 7 11 388 56 82 36 96 128 256), losses := [] }

theorem u923 : Upper (D 6) (R 6) [6,9,384,48,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b923 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b924 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 11 388 104 52 33 66 208 336), lower := (rows 7 11 388 104 52 33 66 128 256), losses := [] }

theorem u924 : Upper (D 6) (R 6) [6,9,384,96,36,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b924 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b925 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 391, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 388 104 52 33 80 194 322), lower := (rows 7 11 388 104 52 33 80 128 256), losses := [] }

theorem u925 : Upper (D 6) (R 6) [6,9,384,96,36,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b925 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b926 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 434, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 37 76 400 96 65 162 290), lower := (rows 7 26 37 76 400 96 65 128 256), losses := [] }

theorem u926 : Upper (D 6) (R 6) [6,24,33,68,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b926 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b927 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 400, targets := 66 },{ cop := 0, region := 72, targets := 1 }], pairs := [(3,0),(4,1),(4,6)], upper := (rows 7 26 37 76 400 96 66 161 289), lower := (rows 7 26 37 76 400 96 66 128 256), losses := [] }

theorem u927 : Upper (D 6) (R 6) [6,24,33,68,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b927 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b928 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 403, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 7 26 37 76 400 96 96 131 259), lower := (rows 7 26 37 76 400 96 96 128 256), losses := [] }

theorem u928 : Upper (D 6) (R 6) [6,24,33,68,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b928 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b929 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 136, targets := 66 },{ cop := 0, region := 368, targets := 1 }], pairs := [(3,1),(3,6),(4,0)], upper := (rows 7 26 37 137 336 96 66 164 292), lower := (rows 7 26 37 137 336 96 66 128 256), losses := [] }

theorem u929 : Upper (D 6) (R 6) [6,24,33,129,320,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b929 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b930 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 26 37 137 336 96 68 162 290), lower := (rows 7 26 37 137 336 96 68 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 29 125 69 139 267), good := (rows 502 442 500 506 368 96 116 128 256) }] }

theorem u930 : Upper (D 6) (R 6) [6,24,33,129,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b930 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b931 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 26 37 137 336 96 96 134 262), lower := (rows 7 26 37 137 336 96 96 128 256), losses := [] }

theorem u931 : Upper (D 6) (R 6) [6,24,33,129,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b931 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b932 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,0),(2,1),(4,2)], upper := (rows 7 26 37 140 336 96 65 162 290), lower := (rows 7 26 37 140 336 96 65 128 256), losses := [{ target := 0, region := (rows 0 70 4 13 112 112 64 246 374), good := (rows 398 442 446 398 498 498 506 128 256) }] }

theorem u932 : Upper (D 6) (R 6) [6,24,33,132,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b932 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b933 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 136, targets := 66 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(3,6),(4,2)], upper := (rows 7 26 37 140 336 96 66 161 289), lower := (rows 7 26 37 140 336 96 66 128 256), losses := [] }

theorem u933 : Upper (D 6) (R 6) [6,24,33,132,320,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b933 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b934 : PairBound 9 := { available := 3, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 7 26 37 140 336 96 96 131 259), lower := (rows 7 26 37 140 336 96 96 128 256), losses := [] }

theorem u934 : Upper (D 6) (R 6) [6,24,33,132,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b934 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b935 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,0),(2,1),(4,5)], upper := (rows 7 26 37 168 336 96 65 134 262), lower := (rows 7 26 37 168 336 96 65 128 256), losses := [{ target := 0, region := (rows 0 114 4 76 80 112 64 133 261), good := (rows 398 58 430 170 378 122 506 128 256) }] }

theorem u935 : Upper (D 6) (R 6) [6,24,33,160,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b935 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b936 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 136, targets := 66 },{ cop := 0, region := 336, targets := 32 }], pairs := [(3,1),(3,6),(4,5)], upper := (rows 7 26 37 168 336 96 66 133 261), lower := (rows 7 26 37 168 336 96 66 128 256), losses := [] }

theorem u936 : Upper (D 6) (R 6) [6,24,33,160,320,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b936 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b937 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 336, targets := 32 }], pairs := [(1,2),(2,1),(4,5)], upper := (rows 7 26 37 168 336 96 68 131 259), lower := (rows 7 26 37 168 336 96 68 128 256), losses := [{ target := 2, region := (rows 1 114 0 76 80 112 64 133 261), good := (rows 395 58 427 170 378 122 506 128 256) }] }

theorem u937 : Upper (D 6) (R 6) [6,24,33,160,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b937 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b938 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 7 26 100 137 273 34 68 224 352), lower := (rows 7 26 100 137 273 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 36 9 17 32 101 164 292), good := (rows 477 24 484 217 345 484 452 128 256) }] }

theorem u938 : Upper (D 6) (R 6) [6,24,96,129,257,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b938 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b939 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 26 100 137 273 36 96 194 322), lower := (rows 7 26 100 137 273 36 96 128 256), losses := [] }

theorem u939 : Upper (D 6) (R 6) [6,24,96,129,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b939 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b940 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 272, targets := 3 },{ cop := 0, region := 232, targets := 4 }], pairs := [(3,2),(4,0),(4,1)], upper := (rows 7 26 100 137 276 33 66 224 352), lower := (rows 7 26 100 137 276 33 66 128 256), losses := [] }

theorem u940 : Upper (D 6) (R 6) [6,24,96,129,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b940 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b941 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 26 100 137 276 33 96 194 322), lower := (rows 7 26 100 137 276 33 96 128 256), losses := [] }

theorem u941 : Upper (D 6) (R 6) [6,24,96,129,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b941 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b942 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 26 100 137 276 34 96 193 321), lower := (rows 7 26 100 137 276 34 96 128 256), losses := [] }

theorem u942 : Upper (D 6) (R 6) [6,24,96,129,260,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b942 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b943 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 2, region := 272, targets := 1 }], pairs := [(3,1),(3,5),(4,0)], upper := (rows 7 26 100 137 304 34 65 196 324), lower := (rows 7 26 100 137 304 34 65 128 256), losses := [] }

theorem u943 : Upper (D 6) (R 6) [6,24,96,129,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b943 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b944 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 200, targets := 34 },{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0),(3,1),(3,5)], upper := (rows 7 26 100 137 304 34 68 193 321), lower := (rows 7 26 100 137 304 34 68 128 256), losses := [] }

theorem u944 : Upper (D 6) (R 6) [6,24,96,129,288,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b944 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b945 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 26 100 140 304 33 65 194 322), lower := (rows 7 26 100 140 304 33 65 128 256), losses := [] }

theorem u945 : Upper (D 6) (R 6) [6,24,96,132,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b945 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b946 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,0),(3,5),(4,2)], upper := (rows 7 26 100 140 304 33 66 193 321), lower := (rows 7 26 100 140 304 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 36 8 16 32 67 128 256), good := (rows 70 90 100 140 308 100 66 128 256) }] }

theorem u946 : Upper (D 6) (R 6) [6,24,96,132,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b946 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b947 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 132, targets := 66 },{ cop := 0, region := 368, targets := 1 }], pairs := [(2,1),(2,6),(4,0)], upper := (rows 7 26 133 41 336 96 66 164 292), lower := (rows 7 26 133 41 336 96 66 128 256), losses := [] }

theorem u947 : Upper (D 6) (R 6) [6,24,129,33,320,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b947 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b948 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 104, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 7 26 133 41 336 96 68 162 290), lower := (rows 7 26 133 41 336 96 68 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 29 125 69 139 267), good := (rows 502 442 500 506 368 96 116 128 256) }] }

theorem u948 : Upper (D 6) (R 6) [6,24,129,33,320,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b948 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b949 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 26 133 41 336 96 96 134 262), lower := (rows 7 26 133 41 336 96 96 128 256), losses := [] }

theorem u949 : Upper (D 6) (R 6) [6,24,129,33,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b949 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b950 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 104, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,2),(3,1),(4,2)], upper := (rows 7 26 133 44 336 96 65 162 290), lower := (rows 7 26 133 44 336 96 65 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 93 125 69 139 267), good := (rows 499 442 497 506 368 112 497 128 256) }] }

theorem u950 : Upper (D 6) (R 6) [6,24,129,36,320,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b950 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b951 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 104, targets := 1 },{ cop := 0, region := 368, targets := 4 }], pairs := [(1,2),(3,0),(4,2)], upper := (rows 7 26 133 44 336 96 66 161 289), lower := (rows 7 26 133 44 336 96 66 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 29 127 75 133 261), good := (rows 499 122 497 506 368 96 98 128 256) }] }

theorem u951 : Upper (D 6) (R 6) [6,24,129,36,320,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b951 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b952 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 133, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 26 133 44 336 96 96 131 259), lower := (rows 7 26 133 44 336 96 96 128 256), losses := [] }

theorem u952 : Upper (D 6) (R 6) [6,24,129,36,320,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b952 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r953 : Route 9 := (fun mask => (mask,id))

def c953 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u953 : Upper (D 6) (R 6) [6,24,129,96,257,2,4] 13 := by
  apply FastRouting.sound _ _ [6,24,129,96,257,2,4] 13 (by decide) (choices 1) [32,64] r953 c953
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u50
  · exact u51

def b954 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 26 133 104 273 34 96 196 324), lower := (rows 7 26 133 104 273 34 96 128 256), losses := [] }

theorem u954 : Upper (D 6) (R 6) [6,24,129,96,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b954 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b955 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 26 133 104 273 36 96 194 322), lower := (rows 7 26 133 104 273 36 96 128 256), losses := [] }

theorem u955 : Upper (D 6) (R 6) [6,24,129,96,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b955 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b956 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 274, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 133 104 274 33 68 224 352), lower := (rows 7 26 133 104 274 33 68 128 256), losses := [] }

theorem u956 : Upper (D 6) (R 6) [6,24,129,96,258,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b956 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b957 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 26 133 104 274 33 96 196 324), lower := (rows 7 26 133 104 274 33 96 128 256), losses := [] }

theorem u957 : Upper (D 6) (R 6) [6,24,129,96,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b957 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b958 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 7 26 133 104 274 36 96 193 321), lower := (rows 7 26 133 104 274 36 96 128 256), losses := [] }

theorem u958 : Upper (D 6) (R 6) [6,24,129,96,258,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b958 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b959 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 104, targets := 4 }], pairs := [(1,2),(3,0),(3,2)], upper := (rows 7 26 133 104 276 33 66 224 352), lower := (rows 7 26 133 104 276 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 40 16 32 67 168 296), good := (rows 70 474 196 488 276 488 66 128 256) },{ target := 2, region := (rows 1 18 0 61 16 37 83 189 317), good := (rows 491 474 489 488 506 489 66 128 256) }] }

theorem u959 : Upper (D 6) (R 6) [6,24,129,96,260,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b959 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u959
end Delivery.IrregularNine14.P06

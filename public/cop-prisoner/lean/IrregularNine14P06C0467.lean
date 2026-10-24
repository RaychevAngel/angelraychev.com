import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0153

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b28020 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 26 37 11 208 356 356 484 356), lower := (rows 7 26 37 11 208 32 64 128 256), losses := [] }

theorem u28020 : Upper (D 6) (R 6) [6,24,33,3,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28020 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28021 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 7 26 37 11 400 100 100 228 356), lower := (rows 7 26 37 11 400 32 64 128 256), losses := [] }

theorem u28021 : Upper (D 6) (R 6) [6,24,33,3,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28021 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28022 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 498, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 37 13 82 480 480 480 480), lower := (rows 7 26 37 13 82 32 64 128 256), losses := [] }

theorem u28022 : Upper (D 6) (R 6) [6,24,33,5,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28022 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28023 : PairBound 9 := { available := 450, camps := [{ cop := 3, region := 498, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 37 13 112 482 450 450 450), lower := (rows 7 26 37 13 112 32 64 128 256), losses := [] }

theorem u28023 : Upper (D 6) (R 6) [6,24,33,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28023 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28024 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 498, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 37 13 146 352 352 480 352), lower := (rows 7 26 37 13 146 32 64 128 256), losses := [] }

theorem u28024 : Upper (D 6) (R 6) [6,24,33,5,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28024 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28025 : PairBound 9 := { available := 322, camps := [{ cop := 3, region := 498, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 37 13 176 354 322 450 322), lower := (rows 7 26 37 13 176 32 64 128 256), losses := [] }

theorem u28025 : Upper (D 6) (R 6) [6,24,33,5,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28025 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28026 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 498, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 37 13 208 354 354 482 354), lower := (rows 7 26 37 13 208 32 64 128 256), losses := [] }

theorem u28026 : Upper (D 6) (R 6) [6,24,33,5,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28026 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28027 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 498, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 7 26 37 13 400 98 98 226 354), lower := (rows 7 26 37 13 400 32 64 128 256), losses := [] }

theorem u28027 : Upper (D 6) (R 6) [6,24,33,5,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28027 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28028 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 37 14 81 480 480 480 480), lower := (rows 7 26 37 14 81 32 64 128 256), losses := [] }

theorem u28028 : Upper (D 6) (R 6) [6,24,33,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28028 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28029 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 37 14 112 481 449 449 449), lower := (rows 7 26 37 14 112 32 64 128 256), losses := [] }

theorem u28029 : Upper (D 6) (R 6) [6,24,33,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28029 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28030 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 37 14 145 352 352 480 352), lower := (rows 7 26 37 14 145 32 64 128 256), losses := [] }

theorem u28030 : Upper (D 6) (R 6) [6,24,33,6,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28030 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28031 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 15, targets := 64 }], pairs := [(0,6),(1,6),(2,6)], upper := (rows 7 26 37 14 176 353 321 449 321), lower := (rows 7 26 37 14 176 32 64 128 256), losses := [] }

theorem u28031 : Upper (D 6) (R 6) [6,24,33,6,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28031 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28032 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 37 14 208 353 353 481 353), lower := (rows 7 26 37 14 208 32 64 128 256), losses := [] }

theorem u28032 : Upper (D 6) (R 6) [6,24,33,6,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28032 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28033 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 8, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 37 14 400 97 97 225 353), lower := (rows 7 26 37 14 400 32 64 128 256), losses := [] }

theorem u28033 : Upper (D 6) (R 6) [6,24,33,6,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28033 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28034 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 492, targets := 2 },{ cop := 0, region := 464, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 26 37 41 82 484 452 452 452), lower := (rows 7 26 37 41 82 32 64 128 256), losses := [] }

theorem u28034 : Upper (D 6) (R 6) [6,24,33,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28034 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28035 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 8, targets := 66 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 7 26 37 41 84 482 450 450 450), lower := (rows 7 26 37 41 84 32 64 128 256), losses := [] }

theorem u28035 : Upper (D 6) (R 6) [6,24,33,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28035 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28036 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 464, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 26 37 41 146 356 324 452 324), lower := (rows 7 26 37 41 146 32 64 128 256), losses := [] }

theorem u28036 : Upper (D 6) (R 6) [6,24,33,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28036 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28037 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 8, targets := 66 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 7 26 37 41 148 354 322 450 322), lower := (rows 7 26 37 41 148 32 64 128 256), losses := [] }

theorem u28037 : Upper (D 6) (R 6) [6,24,33,33,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28037 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28038 : PairBound 9 := { available := 326, camps := [{ cop := 2, region := 8, targets := 66 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 7 26 37 41 208 358 326 454 326), lower := (rows 7 26 37 41 208 32 64 128 256), losses := [] }

theorem u28038 : Upper (D 6) (R 6) [6,24,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28038 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28039 : PairBound 9 := { available := 70, camps := [{ cop := 2, region := 8, targets := 66 },{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1),(3,1),(3,6)], upper := (rows 7 26 37 41 400 102 70 198 326), lower := (rows 7 26 37 41 400 32 64 128 256), losses := [] }

theorem u28039 : Upper (D 6) (R 6) [6,24,33,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28039 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28040 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 5, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 7 26 37 42 81 484 452 452 452), lower := (rows 7 26 37 42 81 32 64 128 256), losses := [] }

theorem u28040 : Upper (D 6) (R 6) [6,24,33,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28040 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28041 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 5, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 7 26 37 42 84 481 449 449 449), lower := (rows 7 26 37 42 84 32 64 128 256), losses := [] }

theorem u28041 : Upper (D 6) (R 6) [6,24,33,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28041 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28042 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 5, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 7 26 37 42 145 356 324 452 324), lower := (rows 7 26 37 42 145 32 64 128 256), losses := [] }

theorem u28042 : Upper (D 6) (R 6) [6,24,33,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28042 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28043 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 5, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 7 26 37 42 148 353 321 449 321), lower := (rows 7 26 37 42 148 32 64 128 256), losses := [] }

theorem u28043 : Upper (D 6) (R 6) [6,24,33,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28043 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28044 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 5, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 7 26 37 42 208 357 325 453 325), lower := (rows 7 26 37 42 208 32 64 128 256), losses := [] }

theorem u28044 : Upper (D 6) (R 6) [6,24,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28044 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28045 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 5, targets := 64 }], pairs := [(0,6),(2,1),(4,1)], upper := (rows 7 26 37 42 400 101 69 197 325), lower := (rows 7 26 37 42 400 32 64 128 256), losses := [] }

theorem u28045 : Upper (D 6) (R 6) [6,24,33,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28045 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28046 : PairBound 9 := { available := 450, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 37 44 81 482 450 450 450), lower := (rows 7 26 37 44 81 32 64 128 256), losses := [] }

theorem u28046 : Upper (D 6) (R 6) [6,24,33,36,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28046 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28047 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 26 37 44 82 481 449 449 449), lower := (rows 7 26 37 44 82 32 64 128 256), losses := [] }

theorem u28047 : Upper (D 6) (R 6) [6,24,33,36,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28047 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28048 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 37 44 145 354 322 450 322), lower := (rows 7 26 37 44 145 32 64 128 256), losses := [] }

theorem u28048 : Upper (D 6) (R 6) [6,24,33,36,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28048 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28049 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 467, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 7 26 37 44 146 353 321 449 321), lower := (rows 7 26 37 44 146 32 64 128 256), losses := [] }

theorem u28049 : Upper (D 6) (R 6) [6,24,33,36,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28049 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28050 : PairBound 9 := { available := 323, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 37 44 208 355 323 451 323), lower := (rows 7 26 37 44 208 32 64 128 256), losses := [] }

theorem u28050 : Upper (D 6) (R 6) [6,24,33,36,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28050 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28051 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 7 26 37 44 400 99 67 195 323), lower := (rows 7 26 37 44 400 32 64 128 256), losses := [] }

theorem u28051 : Upper (D 6) (R 6) [6,24,33,36,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28051 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28052 : PairBound 9 := { available := 420, camps := [{ cop := 3, region := 18, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 7 26 37 73 82 420 484 420 420), lower := (rows 7 26 37 73 82 32 64 128 256), losses := [] }

theorem u28052 : Upper (D 6) (R 6) [6,24,33,65,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28052 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28053 : PairBound 9 := { available := 418, camps := [{ cop := 4, region := 11, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 7 26 37 73 84 418 482 418 418), lower := (rows 7 26 37 73 84 32 64 128 256), losses := [] }

theorem u28053 : Upper (D 6) (R 6) [6,24,33,65,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28053 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28054 : PairBound 9 := { available := 390, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 7 26 37 73 112 422 454 390 390), lower := (rows 7 26 37 73 112 32 64 128 256), losses := [] }

theorem u28054 : Upper (D 6) (R 6) [6,24,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28054 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28055 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 496, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 26 37 73 146 356 356 484 356), lower := (rows 7 26 37 73 146 32 64 128 256), losses := [] }

theorem u28055 : Upper (D 6) (R 6) [6,24,33,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28055 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28056 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 0, region := 360, targets := 4 }], pairs := [(1,0),(3,2),(4,0)], upper := (rows 7 26 37 73 148 354 354 482 354), lower := (rows 7 26 37 73 148 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 21 43 75 139 267), good := (rows 502 506 500 506 148 32 64 128 256) }] }

theorem u28056 : Upper (D 6) (R 6) [6,24,33,65,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28056 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28057 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 496, targets := 1 },{ cop := 0, region := 328, targets := 32 }], pairs := [(1,0),(3,5),(4,0)], upper := (rows 7 26 37 73 176 358 326 454 326), lower := (rows 7 26 37 73 176 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 29 33 65 129 257), good := (rows 502 26 500 506 176 32 64 128 256) }] }

theorem u28057 : Upper (D 6) (R 6) [6,24,33,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28057 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28058 : PairBound 9 := { available := 294, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 0, region := 496, targets := 1 }], pairs := [(0,6),(2,6),(4,0)], upper := (rows 7 26 37 73 208 294 358 422 294), lower := (rows 7 26 37 73 208 32 64 128 256), losses := [] }

theorem u28058 : Upper (D 6) (R 6) [6,24,33,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28058 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28059 : Route 9 := (fun mask => (mask,id))

def c28059 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28059 : Upper (D 6) (R 6) [6,24,33,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,384] 13 (by decide) (choices 1) [2,4,64] r28059 c28059
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9224
  · exact u9225
  · exact u9226

def b28060 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 10, targets := 5 }], pairs := [(1,0),(1,2),(3,0)], upper := (rows 7 26 37 74 84 417 481 417 417), lower := (rows 7 26 37 74 84 32 64 128 256), losses := [] }

theorem u28060 : Upper (D 6) (R 6) [6,24,33,66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28060 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28061 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 7 26 37 74 112 421 453 389 389), lower := (rows 7 26 37 74 112 32 64 128 256), losses := [] }

theorem u28061 : Upper (D 6) (R 6) [6,24,33,66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28061 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28062 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 360, targets := 1 }], pairs := [(2,1),(3,0),(4,1)], upper := (rows 7 26 37 74 145 356 356 484 356), lower := (rows 7 26 37 74 145 32 64 128 256), losses := [] }

theorem u28062 : Upper (D 6) (R 6) [6,24,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28062 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28063 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 360, targets := 4 }], pairs := [(2,1),(3,2),(4,1)], upper := (rows 7 26 37 74 148 353 353 481 353), lower := (rows 7 26 37 74 148 32 64 128 256), losses := [] }

theorem u28063 : Upper (D 6) (R 6) [6,24,33,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28063 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28064 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 328, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 26 37 74 176 357 325 453 325), lower := (rows 7 26 37 74 176 32 64 128 256), losses := [] }

theorem u28064 : Upper (D 6) (R 6) [6,24,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28064 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28065 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 10, targets := 37 }], pairs := [(1,0),(1,2),(1,5)], upper := (rows 7 26 37 74 208 293 357 421 293), lower := (rows 7 26 37 74 208 32 64 128 256), losses := [] }

theorem u28065 : Upper (D 6) (R 6) [6,24,33,66,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28065 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28066 : Route 9 := (fun mask => (mask,id))

def c28066 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28066 : Upper (D 6) (R 6) [6,24,33,66,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66,384] 13 (by decide) (choices 1) [1,4,64] r28066 c28066
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9227
  · exact u9228
  · exact u9229

def b28067 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 496, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 26 37 76 112 419 451 387 387), lower := (rows 7 26 37 76 112 32 64 128 256), losses := [] }

theorem u28067 : Upper (D 6) (R 6) [6,24,33,68,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28067 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28068 : PairBound 9 := { available := 354, camps := [{ cop := 0, region := 360, targets := 1 },{ cop := 0, region := 496, targets := 4 }], pairs := [(1,0),(3,0),(4,2)], upper := (rows 7 26 37 76 145 354 354 482 354), lower := (rows 7 26 37 76 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 13 16 51 83 147 275), good := (rows 494 506 492 76 506 32 64 128 256) }] }

theorem u28068 : Upper (D 6) (R 6) [6,24,33,68,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28068 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28069 : PairBound 9 := { available := 353, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 496, targets := 4 }], pairs := [(2,1),(3,1),(4,2)], upper := (rows 7 26 37 76 146 353 353 481 353), lower := (rows 7 26 37 76 146 32 64 128 256), losses := [] }

theorem u28069 : Upper (D 6) (R 6) [6,24,33,68,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28069 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28070 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 496, targets := 4 },{ cop := 0, region := 328, targets := 32 }], pairs := [(1,2),(3,5),(4,2)], upper := (rows 7 26 37 76 176 355 323 451 323), lower := (rows 7 26 37 76 176 32 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 21 33 65 129 257), good := (rows 499 26 497 90 176 32 64 128 256) }] }

theorem u28070 : Upper (D 6) (R 6) [6,24,33,68,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28070 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28071 : PairBound 9 := { available := 291, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 0, region := 496, targets := 4 }], pairs := [(0,6),(2,6),(4,2)], upper := (rows 7 26 37 76 208 291 355 419 291), lower := (rows 7 26 37 76 208 32 64 128 256), losses := [] }

theorem u28071 : Upper (D 6) (R 6) [6,24,33,68,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28071 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28072 : Route 9 := (fun mask => (mask,id))

def c28072 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28072 : Upper (D 6) (R 6) [6,24,33,68,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,68,384] 13 (by decide) (choices 1) [1,2,64] r28072 c28072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u9230
  · exact u9231
  · exact u9232

def b28073 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 360, targets := 1 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,0),(3,0),(4,5)], upper := (rows 7 26 37 104 145 358 326 454 326), lower := (rows 7 26 37 104 145 32 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 29 16 33 65 129 257), good := (rows 494 26 492 104 506 32 64 128 256) }] }

theorem u28073 : Upper (D 6) (R 6) [6,24,33,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28073 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28074 : PairBound 9 := { available := 325, camps := [{ cop := 0, region := 364, targets := 2 },{ cop := 0, region := 464, targets := 32 }], pairs := [(2,1),(3,1),(4,5)], upper := (rows 7 26 37 104 146 357 325 453 325), lower := (rows 7 26 37 104 146 32 64 128 256), losses := [] }

theorem u28074 : Upper (D 6) (R 6) [6,24,33,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28074 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28075 : PairBound 9 := { available := 323, camps := [{ cop := 0, region := 360, targets := 4 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,2),(3,2),(4,5)], upper := (rows 7 26 37 104 148 355 323 451 323), lower := (rows 7 26 37 104 148 32 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 13 16 33 65 129 257), good := (rows 491 26 489 104 154 32 64 128 256) }] }

theorem u28075 : Upper (D 6) (R 6) [6,24,33,96,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28075 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28076 : PairBound 9 := { available := 263, camps := [{ cop := 1, region := 293, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(0,6),(2,6),(4,5)], upper := (rows 7 26 37 104 208 295 327 391 263), lower := (rows 7 26 37 104 208 32 64 128 256), losses := [] }

theorem u28076 : Upper (D 6) (R 6) [6,24,33,96,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28076 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r28077 : Route 9 := (fun mask => (mask,id))

def c28077 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u28077 : Upper (D 6) (R 6) [6,24,33,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,384] 13 (by decide) (choices 1) [1,2,4,64] r28077 c28077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u9233
  · exact u9234
  · exact u9235
  · exact u9236

def b28078 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 236, targets := 2 },{ cop := 0, region := 368, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 26 37 137 274 100 100 228 356), lower := (rows 7 26 37 137 274 32 64 128 256), losses := [] }

theorem u28078 : Upper (D 6) (R 6) [6,24,33,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28078 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b28079 : PairBound 9 := { available := 98, camps := [{ cop := 0, region := 368, targets := 1 },{ cop := 0, region := 232, targets := 4 }], pairs := [(1,0),(3,2),(4,0)], upper := (rows 7 26 37 137 276 98 98 226 354), lower := (rows 7 26 37 137 276 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 21 43 75 139 267), good := (rows 502 506 500 506 276 32 64 128 256) }] }

theorem u28079 : Upper (D 6) (R 6) [6,24,33,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b28079 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u28079
end Delivery.IrregularNine14.P06

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0097

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b19500 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 100 140 276 33 90 154 282), lower := (rows 35 67 100 140 276 33 64 128 256), losses := [] }

theorem u19500 : Upper (D 6) (R 6) [34,65,96,132,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19500 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19501 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 140 276 34 89 153 281), lower := (rows 35 67 100 140 276 34 64 128 256), losses := [] }

theorem u19501 : Upper (D 6) (R 6) [34,65,96,132,260,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19501 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19502 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 100 140 276 40 83 147 275), lower := (rows 35 67 100 140 276 40 64 128 256), losses := [] }

theorem u19502 : Upper (D 6) (R 6) [34,65,96,132,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19502 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19503 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 100 140 280 33 86 150 278), lower := (rows 35 67 100 140 280 33 64 128 256), losses := [] }

theorem u19503 : Upper (D 6) (R 6) [34,65,96,132,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19503 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19504 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 140 280 34 85 149 277), lower := (rows 35 67 100 140 280 34 64 128 256), losses := [] }

theorem u19504 : Upper (D 6) (R 6) [34,65,96,132,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19505 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 6, region := 36, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 140 280 36 83 147 275), lower := (rows 35 67 100 140 280 36 64 128 256), losses := [] }

theorem u19505 : Upper (D 6) (R 6) [34,65,96,132,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19506 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 3, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 100 140 280 48 71 135 263), lower := (rows 35 67 100 140 280 48 64 128 256), losses := [] }

theorem u19506 : Upper (D 6) (R 6) [34,65,96,132,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19506 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19507 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 67 100 152 280 33 70 134 262), lower := (rows 35 67 100 152 280 33 64 128 256), losses := [] }

theorem u19507 : Upper (D 6) (R 6) [34,65,96,144,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19508 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 100 152 280 34 69 133 261), lower := (rows 35 67 100 152 280 34 64 128 256), losses := [] }

theorem u19508 : Upper (D 6) (R 6) [34,65,96,144,264,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19508 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19509 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 3, targets := 4 },{ cop := 6, region := 36, targets := 1 }], pairs := [(0,2),(1,2),(2,0)], upper := (rows 35 67 100 152 280 36 71 135 263), lower := (rows 35 67 100 152 280 36 64 128 256), losses := [] }

theorem u19509 : Upper (D 6) (R 6) [34,65,96,144,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19509 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19510 : PairBound 9 := { available := 336, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 14 52 40 336 464 336), lower := (rows 35 67 133 14 52 40 64 128 256), losses := [] }

theorem u19510 : Upper (D 6) (R 6) [34,65,129,6,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19510 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19511 : PairBound 9 := { available := 328, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5),(2,5)], upper := (rows 35 67 133 14 52 48 328 456 328), lower := (rows 35 67 133 14 52 48 64 128 256), losses := [] }

theorem u19511 : Upper (D 6) (R 6) [34,65,129,6,36,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19511 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19512 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 14 52 96 344 408 280), lower := (rows 35 67 133 14 52 96 64 128 256), losses := [] }

theorem u19512 : Upper (D 6) (R 6) [34,65,129,6,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19513 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 14 52 288 88 216 344), lower := (rows 35 67 133 14 52 288 64 128 256), losses := [] }

theorem u19513 : Upper (D 6) (R 6) [34,65,129,6,36,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19513 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19514 : PairBound 9 := { available := 336, camps := [{ cop := 3, region := 48, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 67 133 14 56 36 336 464 336), lower := (rows 35 67 133 14 56 36 64 128 256), losses := [] }

theorem u19514 : Upper (D 6) (R 6) [34,65,129,6,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19514 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19515 : PairBound 9 := { available := 324, camps := [{ cop := 3, region := 49, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 67 133 14 56 48 324 452 324), lower := (rows 35 67 133 14 56 48 64 128 256), losses := [] }

theorem u19515 : Upper (D 6) (R 6) [34,65,129,6,40,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19515 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19516 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 14 56 96 340 404 276), lower := (rows 35 67 133 14 56 96 64 128 256), losses := [] }

theorem u19516 : Upper (D 6) (R 6) [34,65,129,6,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19517 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 14 56 288 84 212 340), lower := (rows 35 67 133 14 56 288 64 128 256), losses := [] }

theorem u19517 : Upper (D 6) (R 6) [34,65,129,6,40,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19517 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19518 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 14 84 40 368 432 304), lower := (rows 35 67 133 14 84 40 64 128 256), losses := [] }

theorem u19518 : Upper (D 6) (R 6) [34,65,129,6,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19518 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19519 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 133 14 84 48 360 424 296), lower := (rows 35 67 133 14 84 48 64 128 256), losses := [] }

theorem u19519 : Upper (D 6) (R 6) [34,65,129,6,68,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19519 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19520 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 14 84 288 120 184 312), lower := (rows 35 67 133 14 84 288 64 128 256), losses := [] }

theorem u19520 : Upper (D 6) (R 6) [34,65,129,6,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19520 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19521 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 368, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 67 133 14 88 36 368 432 304), lower := (rows 35 67 133 14 88 36 64 128 256), losses := [] }

theorem u19521 : Upper (D 6) (R 6) [34,65,129,6,72,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19522 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 133 14 88 48 356 420 292), lower := (rows 35 67 133 14 88 48 64 128 256), losses := [] }

theorem u19522 : Upper (D 6) (R 6) [34,65,129,6,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19522 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19523 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 14 88 288 116 180 308), lower := (rows 35 67 133 14 88 288 64 128 256), losses := [] }

theorem u19523 : Upper (D 6) (R 6) [34,65,129,6,72,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19523 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19524 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 14 276 40 112 240 368), lower := (rows 35 67 133 14 276 40 64 128 256), losses := [] }

theorem u19524 : Upper (D 6) (R 6) [34,65,129,6,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19524 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19525 : PairBound 9 := { available := 104, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 14 276 48 104 232 360), lower := (rows 35 67 133 14 276 48 64 128 256), losses := [] }

theorem u19525 : Upper (D 6) (R 6) [34,65,129,6,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19525 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19526 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 14 276 96 120 184 312), lower := (rows 35 67 133 14 276 96 64 128 256), losses := [] }

theorem u19526 : Upper (D 6) (R 6) [34,65,129,6,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19527 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 368, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 67 133 14 280 36 112 240 368), lower := (rows 35 67 133 14 280 36 64 128 256), losses := [] }

theorem u19527 : Upper (D 6) (R 6) [34,65,129,6,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19527 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19528 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 368, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 14 280 48 100 228 356), lower := (rows 35 67 133 14 280 48 64 128 256), losses := [] }

theorem u19528 : Upper (D 6) (R 6) [34,65,129,6,264,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19528 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19529 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 14 280 96 116 180 308), lower := (rows 35 67 133 14 280 96 64 128 256), losses := [] }

theorem u19529 : Upper (D 6) (R 6) [34,65,129,6,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19530 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 368, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 67 133 14 304 36 88 216 344), lower := (rows 35 67 133 14 304 36 64 128 256), losses := [] }

theorem u19530 : Upper (D 6) (R 6) [34,65,129,6,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19531 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 14 304 40 84 212 340), lower := (rows 35 67 133 14 304 40 64 128 256), losses := [] }

theorem u19531 : Upper (D 6) (R 6) [34,65,129,6,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19531 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19532 : PairBound 9 := { available := 76, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 35 67 133 14 304 48 76 204 332), lower := (rows 35 67 133 14 304 48 64 128 256), losses := [] }

theorem u19532 : Upper (D 6) (R 6) [34,65,129,6,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19532 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19533 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 14 304 96 92 156 284), lower := (rows 35 67 133 14 304 96 64 128 256), losses := [] }

theorem u19533 : Upper (D 6) (R 6) [34,65,129,6,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19533 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19534 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 368, targets := 3 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(4,0),(4,1)], upper := (rows 35 67 133 14 336 36 120 184 312), lower := (rows 35 67 133 14 336 36 64 128 256), losses := [] }

theorem u19534 : Upper (D 6) (R 6) [34,65,129,6,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19535 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 14 336 40 116 180 308), lower := (rows 35 67 133 14 336 40 64 128 256), losses := [] }

theorem u19535 : Upper (D 6) (R 6) [34,65,129,6,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19535 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19536 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 133 14 336 48 108 172 300), lower := (rows 35 67 133 14 336 48 64 128 256), losses := [] }

theorem u19536 : Upper (D 6) (R 6) [34,65,129,6,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19536 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19537 : PairBound 9 := { available := 352, camps := [{ cop := 5, region := 323, targets := 4 },{ cop := 0, region := 452, targets := 2 }], pairs := [(0,2),(1,2),(2,1)], upper := (rows 35 67 133 26 28 36 352 480 352), lower := (rows 35 67 133 26 28 36 64 128 256), losses := [] }

theorem u19537 : Upper (D 6) (R 6) [34,65,129,18,12,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19538 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 26 28 96 356 420 292), lower := (rows 35 67 133 26 28 96 64 128 256), losses := [] }

theorem u19538 : Upper (D 6) (R 6) [34,65,129,18,12,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19539 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 26 28 288 100 228 356), lower := (rows 35 67 133 26 28 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 8 24 319 95 159 287), good := (rows 485 485 485 508 508 288 64 128 288) }] }

theorem u19539 : Upper (D 6) (R 6) [34,65,129,18,12,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19539 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19540 : PairBound 9 := { available := 328, camps := [{ cop := 2, region := 48, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 35 67 133 26 52 36 328 456 328), lower := (rows 35 67 133 26 52 36 64 128 256), losses := [] }

theorem u19540 : Upper (D 6) (R 6) [34,65,129,18,36,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19541 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 26 52 40 324 452 324), lower := (rows 35 67 133 26 52 40 64 128 256), losses := [] }

theorem u19541 : Upper (D 6) (R 6) [34,65,129,18,36,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19541 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19542 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 26 52 96 332 396 268), lower := (rows 35 67 133 26 52 96 64 128 256), losses := [] }

theorem u19542 : Upper (D 6) (R 6) [34,65,129,18,36,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19543 : Route 9 := (fun mask => (mask,id))

def c19543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19543 : Upper (D 6) (R 6) [34,65,129,18,36,256] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18,36,256] 13 (by decide) (choices 1) [4,8] r19543 c19543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5842
  · exact u5843

def b19544 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,0)], upper := (rows 35 67 133 26 84 36 360 424 296), lower := (rows 35 67 133 26 84 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 52 52 77 141 269), good := (rows 506 458 508 506 500 500 64 128 256) }] }

theorem u19544 : Upper (D 6) (R 6) [34,65,129,18,68,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19545 : PairBound 9 := { available := 292, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 133 26 84 40 356 420 292), lower := (rows 35 67 133 26 84 40 64 128 256), losses := [] }

theorem u19545 : Upper (D 6) (R 6) [34,65,129,18,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19545 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19546 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 67 133 26 84 288 108 172 300), lower := (rows 35 67 133 26 84 288 64 128 256), losses := [] }

theorem u19546 : Upper (D 6) (R 6) [34,65,129,18,68,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19546 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19547 : PairBound 9 := { available := 104, camps := [], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 133 26 276 36 104 232 360), lower := (rows 35 67 133 26 276 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 52 52 77 141 269), good := (rows 506 458 508 506 500 500 64 128 256) },{ target := 6, region := (rows 9 2 4 8 16 52 0 128 256), good := (rows 35 3 165 59 308 36 0 128 256) }] }

theorem u19547 : Upper (D 6) (R 6) [34,65,129,18,260,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19548 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 26 276 40 100 228 356), lower := (rows 35 67 133 26 276 40 64 128 256), losses := [] }

theorem u19548 : Upper (D 6) (R 6) [34,65,129,18,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19548 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19549 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 26 276 96 108 172 300), lower := (rows 35 67 133 26 276 96 64 128 256), losses := [] }

theorem u19549 : Upper (D 6) (R 6) [34,65,129,18,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19550 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 35 67 133 26 280 36 100 228 356), lower := (rows 35 67 133 26 280 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 11 21 36 100 164 292), good := (rows 506 90 508 26 280 500 64 128 256) }] }

theorem u19550 : Upper (D 6) (R 6) [34,65,129,18,264,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19551 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 26 280 96 100 164 292), lower := (rows 35 67 133 26 280 96 64 128 256), losses := [] }

theorem u19551 : Upper (D 6) (R 6) [34,65,129,18,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r19552 : Route 9 := (fun mask => (mask,id))

def c19552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u19552 : Upper (D 6) (R 6) [34,65,129,18,288,4] 13 := by
  apply FastRouting.sound _ _ [34,65,129,18,288,4] 13 (by decide) (choices 1) [4,8] r19552 c19552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5844
  · exact u5845

def b19553 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 468, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 35 67 133 26 304 40 68 196 324), lower := (rows 35 67 133 26 304 40 64 128 256), losses := [] }

theorem u19553 : Upper (D 6) (R 6) [34,65,129,18,288,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19553 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19554 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 26 304 96 76 140 268), lower := (rows 35 67 133 26 304 96 64 128 256), losses := [] }

theorem u19554 : Upper (D 6) (R 6) [34,65,129,18,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19555 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 165, targets := 64 }], pairs := [(0,6),(2,6),(3,0)], upper := (rows 35 67 133 26 336 36 108 172 300), lower := (rows 35 67 133 26 336 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 9 52 36 68 132 260), good := (rows 58 74 508 26 336 500 64 128 256) }] }

theorem u19555 : Upper (D 6) (R 6) [34,65,129,18,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19556 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 43, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 67 133 26 336 40 100 164 292), lower := (rows 35 67 133 26 336 40 64 128 256), losses := [] }

theorem u19556 : Upper (D 6) (R 6) [34,65,129,18,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19556 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19557 : PairBound 9 := { available := 324, camps := [{ cop := 0, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 35 67 133 28 56 34 324 452 324), lower := (rows 35 67 133 28 56 34 64 128 256), losses := [] }

theorem u19557 : Upper (D 6) (R 6) [34,65,129,20,40,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19558 : PairBound 9 := { available := 322, camps := [{ cop := 2, region := 56, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 35 67 133 28 56 36 322 450 322), lower := (rows 35 67 133 28 56 36 64 128 256), losses := [] }

theorem u19558 : Upper (D 6) (R 6) [34,65,129,20,40,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b19559 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 67 133 28 56 96 326 390 262), lower := (rows 35 67 133 28 56 96 64 128 256), losses := [] }

theorem u19559 : Upper (D 6) (R 6) [34,65,129,20,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b19559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u19559
end Delivery.IrregularNine14.P06

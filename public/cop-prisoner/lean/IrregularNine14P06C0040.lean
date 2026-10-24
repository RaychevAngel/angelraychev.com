import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2400 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 133 88 52 288 66 196 324), lower := (rows 11 35 133 88 52 288 66 128 256), losses := [] }

theorem u2400 : Upper (D 6) (R 6) [10,33,129,80,36,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2400 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2401 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 133 88 52 288 68 194 322), lower := (rows 11 35 133 88 52 288 68 128 256), losses := [] }

theorem u2401 : Upper (D 6) (R 6) [10,33,129,80,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2401 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2402 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 35 133 88 276 36 66 224 352), lower := (rows 11 35 133 88 276 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 52 52 67 142 270), good := (rows 458 506 508 504 444 444 458 128 256) }] }

theorem u2402 : Upper (D 6) (R 6) [10,33,129,80,260,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2402 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2403 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 35 133 88 276 36 96 194 322), lower := (rows 11 35 133 88 276 36 96 128 256), losses := [] }

theorem u2403 : Upper (D 6) (R 6) [10,33,129,80,260,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2404 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 133 88 304 36 66 196 324), lower := (rows 11 35 133 88 304 36 66 128 256), losses := [] }

theorem u2404 : Upper (D 6) (R 6) [10,33,129,80,288,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2405 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(2,5),(3,0)], upper := (rows 11 35 133 88 304 36 68 194 322), lower := (rows 11 35 133 88 304 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 26 18 100 100 130 258), good := (rows 410 506 228 120 376 100 100 128 256) }] }

theorem u2405 : Upper (D 6) (R 6) [10,33,129,80,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2405 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2406 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 360, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 133 268 22 96 80 224 352), lower := (rows 11 35 133 268 22 96 80 128 256), losses := [] }

theorem u2406 : Upper (D 6) (R 6) [10,33,129,260,6,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2406 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2407 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 4, region := 360, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 35 133 268 22 96 96 208 336), lower := (rows 11 35 133 268 22 96 96 128 256), losses := [] }

theorem u2407 : Upper (D 6) (R 6) [10,33,129,260,6,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2408 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 35 133 268 52 96 66 208 336), lower := (rows 11 35 133 268 52 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 28 103 67 133 261), good := (rows 506 482 508 444 444 96 98 128 256) }] }

theorem u2408 : Upper (D 6) (R 6) [10,33,129,260,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2409 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 133 268 52 96 80 194 322), lower := (rows 11 35 133 268 52 96 80 128 256), losses := [] }

theorem u2409 : Upper (D 6) (R 6) [10,33,129,260,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2409 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2410 : PairBound 9 := { available := 48, camps := [], pairs := [(3,0),(4,0),(4,5)], upper := (rows 11 35 133 268 82 96 68 176 304), lower := (rows 11 35 133 268 82 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 17 125 76 151 279), good := (rows 506 434 508 492 506 104 492 128 256) },{ target := 5, region := (rows 1 2 4 8 17 0 76 128 256), good := (rows 91 19 213 332 82 64 68 128 256) }] }

theorem u2410 : Upper (D 6) (R 6) [10,33,129,260,66,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2411 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 133 268 82 96 80 164 292), lower := (rows 11 35 133 268 82 96 80 128 256), losses := [] }

theorem u2411 : Upper (D 6) (R 6) [10,33,129,260,66,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2411 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2412 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 397, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 11 35 133 268 82 96 96 148 276), lower := (rows 11 35 133 268 82 96 96 128 256), losses := [] }

theorem u2412 : Upper (D 6) (R 6) [10,33,129,260,66,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2413 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 4, region := 296, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 35 133 268 84 96 66 176 304), lower := (rows 11 35 133 268 84 96 66 128 256), losses := [] }

theorem u2413 : Upper (D 6) (R 6) [10,33,129,260,68,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2414 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 133 268 84 96 80 162 290), lower := (rows 11 35 133 268 84 96 80 128 256), losses := [] }

theorem u2414 : Upper (D 6) (R 6) [10,33,129,260,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2414 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2415 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 11 35 133 268 84 96 96 146 274), lower := (rows 11 35 133 268 84 96 96 128 256), losses := [] }

theorem u2415 : Upper (D 6) (R 6) [10,33,129,260,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2416 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(1,2),(2,5)], upper := (rows 11 35 133 280 52 96 66 196 324), lower := (rows 11 35 133 280 52 96 66 128 256), losses := [] }

theorem u2416 : Upper (D 6) (R 6) [10,33,129,272,36,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2417 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 35 133 280 52 96 68 194 322), lower := (rows 11 35 133 280 52 96 68 128 256), losses := [] }

theorem u2417 : Upper (D 6) (R 6) [10,33,129,272,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2418 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 296, targets := 3 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 35 133 280 84 36 66 224 352), lower := (rows 11 35 133 280 84 36 66 128 256), losses := [] }

theorem u2418 : Upper (D 6) (R 6) [10,33,129,272,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2419 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,1)], upper := (rows 11 35 133 280 84 36 96 194 322), lower := (rows 11 35 133 280 84 36 96 128 256), losses := [] }

theorem u2419 : Upper (D 6) (R 6) [10,33,129,272,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2420 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,2)], upper := (rows 11 35 133 280 112 36 66 196 324), lower := (rows 11 35 133 280 112 36 66 128 256), losses := [] }

theorem u2420 : Upper (D 6) (R 6) [10,33,129,272,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2421 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 133 280 112 36 68 194 322), lower := (rows 11 35 133 280 112 36 68 128 256), losses := [] }

theorem u2421 : Upper (D 6) (R 6) [10,33,129,272,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2422 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(4,0)], upper := (rows 11 35 133 328 82 36 68 176 304), lower := (rows 11 35 133 328 82 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 26 18 100 100 146 274), good := (rows 410 506 228 360 506 100 100 128 256) }] }

theorem u2422 : Upper (D 6) (R 6) [10,33,129,320,66,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2423 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 11 35 133 328 82 36 80 164 292), lower := (rows 11 35 133 328 82 36 80 128 256), losses := [] }

theorem u2423 : Upper (D 6) (R 6) [10,33,129,320,66,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2423 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2424 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 35 133 328 82 36 96 148 276), lower := (rows 11 35 133 328 82 36 96 128 256), losses := [] }

theorem u2424 : Upper (D 6) (R 6) [10,33,129,320,66,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2425 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 296, targets := 3 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(3,0),(3,1)], upper := (rows 11 35 133 328 84 36 66 176 304), lower := (rows 11 35 133 328 84 36 66 128 256), losses := [] }

theorem u2425 : Upper (D 6) (R 6) [10,33,129,320,68,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2426 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 133 328 84 36 80 162 290), lower := (rows 11 35 133 328 84 36 80 128 256), losses := [] }

theorem u2426 : Upper (D 6) (R 6) [10,33,129,320,68,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2426 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2427 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,1)], upper := (rows 11 35 133 328 84 36 96 146 274), lower := (rows 11 35 133 328 84 36 96 128 256), losses := [] }

theorem u2427 : Upper (D 6) (R 6) [10,33,129,320,68,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2428 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 296, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 133 328 84 48 66 164 292), lower := (rows 11 35 133 328 84 48 66 128 256), losses := [] }

theorem u2428 : Upper (D 6) (R 6) [10,33,129,320,68,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2428 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2429 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 133 328 84 48 68 162 290), lower := (rows 11 35 133 328 84 48 68 128 256), losses := [] }

theorem u2429 : Upper (D 6) (R 6) [10,33,129,320,68,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2429 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2430 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 132, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 11 35 133 328 84 48 96 134 262), lower := (rows 11 35 133 328 84 48 96 128 256), losses := [] }

theorem u2430 : Upper (D 6) (R 6) [10,33,129,320,68,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2430 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2431 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 80, targets := 5 },{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6),(4,0),(4,2)], upper := (rows 11 35 133 328 112 36 66 148 276), lower := (rows 11 35 133 328 112 36 66 128 256), losses := [] }

theorem u2431 : Upper (D 6) (R 6) [10,33,129,320,96,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2432 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 133 328 112 36 68 146 274), lower := (rows 11 35 133 328 112 36 68 128 256), losses := [] }

theorem u2432 : Upper (D 6) (R 6) [10,33,129,320,96,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2433 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 167, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 133 328 112 36 80 134 262), lower := (rows 11 35 133 328 112 36 80 128 256), losses := [] }

theorem u2433 : Upper (D 6) (R 6) [10,33,129,320,96,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2433 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2434 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 32 },{ cop := 1, region := 80, targets := 2 }], pairs := [(2,5),(4,1)], upper := (rows 11 35 134 28 112 288 65 196 324), lower := (rows 11 35 134 28 112 288 65 128 256), losses := [] }

theorem u2434 : Upper (D 6) (R 6) [10,33,130,20,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2434 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2435 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1)], upper := (rows 11 35 134 28 112 288 68 193 321), lower := (rows 11 35 134 28 112 288 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 76 21 291 76 129 257), good := (rows 505 433 252 92 120 288 92 128 288) }] }

theorem u2435 : Upper (D 6) (R 6) [10,33,130,20,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2435 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2436 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(1,2),(2,5)], upper := (rows 11 35 134 28 304 96 65 196 324), lower := (rows 11 35 134 28 304 96 65 128 256), losses := [] }

theorem u2436 : Upper (D 6) (R 6) [10,33,130,20,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2437 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 11 35 134 28 304 96 68 193 321), lower := (rows 11 35 134 28 304 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 19 109 76 129 257), good := (rows 505 433 252 124 304 96 108 128 256) }] }

theorem u2437 : Upper (D 6) (R 6) [10,33,130,20,288,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2438 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 134 76 52 288 65 208 336), lower := (rows 11 35 134 76 52 288 65 128 256), losses := [] }

theorem u2438 : Upper (D 6) (R 6) [10,33,130,68,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2438 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2439 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 11 35 134 76 52 288 80 193 321), lower := (rows 11 35 134 76 52 288 80 128 256), losses := [] }

theorem u2439 : Upper (D 6) (R 6) [10,33,130,68,36,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2439 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2440 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 35 134 76 112 288 65 148 276), lower := (rows 11 35 134 76 112 288 65 128 256), losses := [] }

theorem u2440 : Upper (D 6) (R 6) [10,33,130,68,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2440 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2441 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 134 76 112 288 68 145 273), lower := (rows 11 35 134 76 112 288 68 128 256), losses := [] }

theorem u2441 : Upper (D 6) (R 6) [10,33,130,68,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2441 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2442 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 11 35 134 76 112 288 80 133 261), lower := (rows 11 35 134 76 112 288 80 128 256), losses := [] }

theorem u2442 : Upper (D 6) (R 6) [10,33,130,68,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2442 [(5,8),(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2443 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 132, targets := 65 }], pairs := [(2,0),(2,6)], upper := (rows 11 35 134 76 336 48 65 164 292), lower := (rows 11 35 134 76 336 48 65 128 256), losses := [] }

theorem u2443 : Upper (D 6) (R 6) [10,33,130,68,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2443 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2444 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 307, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 134 76 336 48 68 161 289), lower := (rows 11 35 134 76 336 48 68 128 256), losses := [] }

theorem u2444 : Upper (D 6) (R 6) [10,33,130,68,320,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2444 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2445 : PairBound 9 := { available := 5, camps := [{ cop := 8, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 134 76 336 48 96 133 261), lower := (rows 11 35 134 76 336 48 96 128 256), losses := [] }

theorem u2445 : Upper (D 6) (R 6) [10,33,130,68,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2445 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2446 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 35 134 88 52 288 65 196 324), lower := (rows 11 35 134 88 52 288 65 128 256), losses := [] }

theorem u2446 : Upper (D 6) (R 6) [10,33,130,80,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2446 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2447 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 35 134 88 52 288 68 193 321), lower := (rows 11 35 134 88 52 288 68 128 256), losses := [] }

theorem u2447 : Upper (D 6) (R 6) [10,33,130,80,36,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2447 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2448 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 35 134 88 304 36 65 196 324), lower := (rows 11 35 134 88 304 36 65 128 256), losses := [] }

theorem u2448 : Upper (D 6) (R 6) [10,33,130,80,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2449 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 35 134 88 304 36 68 193 321), lower := (rows 11 35 134 88 304 36 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 100 100 128 256), good := (rows 10 98 230 120 376 100 100 128 256) },{ target := 1, region := (rows 1 0 4 126 22 100 100 130 258), good := (rows 409 505 508 120 376 124 124 128 256) }] }

theorem u2449 : Upper (D 6) (R 6) [10,33,130,80,288,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2450 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(1,2),(3,1)], upper := (rows 11 35 134 268 52 96 65 208 336), lower := (rows 11 35 134 268 52 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 28 28 103 67 133 261), good := (rows 505 481 508 444 444 96 481 128 256) }] }

theorem u2450 : Upper (D 6) (R 6) [10,33,130,260,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2451 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 35 134 268 52 96 80 193 321), lower := (rows 11 35 134 268 52 96 80 128 256), losses := [] }

theorem u2451 : Upper (D 6) (R 6) [10,33,130,260,36,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2451 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2452 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(3,1),(4,1)], upper := (rows 11 35 134 268 81 96 68 176 304), lower := (rows 11 35 134 268 81 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 17 125 76 147 275), good := (rows 505 433 492 364 497 96 108 128 256) }] }

theorem u2452 : Upper (D 6) (R 6) [10,33,130,260,65,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2453 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 134 268 81 96 80 164 292), lower := (rows 11 35 134 268 81 96 80 128 256), losses := [] }

theorem u2453 : Upper (D 6) (R 6) [10,33,130,260,65,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2453 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2454 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 115, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 35 134 268 81 96 96 148 276), lower := (rows 11 35 134 268 81 96 96 128 256), losses := [] }

theorem u2454 : Upper (D 6) (R 6) [10,33,130,260,65,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2455 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 4, region := 296, targets := 1 }], pairs := [(0,2),(1,2),(3,0)], upper := (rows 11 35 134 268 84 96 65 176 304), lower := (rows 11 35 134 268 84 96 65 128 256), losses := [] }

theorem u2455 : Upper (D 6) (R 6) [10,33,130,260,68,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2456 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 399, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 11 35 134 268 84 96 80 161 289), lower := (rows 11 35 134 268 84 96 80 128 256), losses := [] }

theorem u2456 : Upper (D 6) (R 6) [10,33,130,260,68,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2456 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2457 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 3, region := 99, targets := 4 }], pairs := [(0,2),(4,0),(4,1)], upper := (rows 11 35 134 268 84 96 96 145 273), lower := (rows 11 35 134 268 84 96 96 128 256), losses := [] }

theorem u2457 : Upper (D 6) (R 6) [10,33,130,260,68,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2458 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 99, targets := 4 },{ cop := 0, region := 196, targets := 32 }], pairs := [(0,2),(1,2),(2,5)], upper := (rows 11 35 134 280 52 96 65 196 324), lower := (rows 11 35 134 280 52 96 65 128 256), losses := [] }

theorem u2458 : Upper (D 6) (R 6) [10,33,130,272,36,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b2459 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 35 134 280 52 96 68 193 321), lower := (rows 11 35 134 280 52 96 68 128 256), losses := [] }

theorem u2459 : Upper (D 6) (R 6) [10,33,130,272,36,64,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b2459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u2459
end Delivery.IrregularNine14.P06

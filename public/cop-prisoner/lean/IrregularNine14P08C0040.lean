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

def b2400 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 194 44 328 176 48 69 133 261), lower := (rows 35 194 44 328 176 48 64 128 256), losses := [] }

theorem u2400 : Upper (D 8) (R 8) [34,192,40,320,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2400 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2401 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 152 273 33 100 164 292), lower := (rows 35 194 76 152 273 33 64 128 256), losses := [] }

theorem u2401 : Upper (D 8) (R 8) [34,192,72,144,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2401 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2402 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 194 76 152 273 36 97 161 289), lower := (rows 35 194 76 152 273 36 64 128 256), losses := [] }

theorem u2402 : Upper (D 8) (R 8) [34,192,72,144,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2402 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2403 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 152 304 33 101 165 293), lower := (rows 35 194 76 152 304 33 64 128 256), losses := [] }

theorem u2403 : Upper (D 8) (R 8) [34,192,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2403 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2404 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 194 76 152 304 36 97 161 289), lower := (rows 35 194 76 152 304 36 64 128 256), losses := [] }

theorem u2404 : Upper (D 8) (R 8) [34,192,72,144,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2404 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2405 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 168 273 33 116 180 308), lower := (rows 35 194 76 168 273 33 64 128 256), losses := [] }

theorem u2405 : Upper (D 8) (R 8) [34,192,72,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2405 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2406 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 194 76 168 273 36 113 177 305), lower := (rows 35 194 76 168 273 36 64 128 256), losses := [] }

theorem u2406 : Upper (D 8) (R 8) [34,192,72,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2406 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2407 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 194 76 168 273 48 101 165 293), lower := (rows 35 194 76 168 273 48 64 128 256), losses := [] }

theorem u2407 : Upper (D 8) (R 8) [34,192,72,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2407 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2408 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 168 276 33 113 177 305), lower := (rows 35 194 76 168 276 33 64 128 256), losses := [] }

theorem u2408 : Upper (D 8) (R 8) [34,192,72,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2408 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2409 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 194 76 168 276 48 97 161 289), lower := (rows 35 194 76 168 276 48 64 128 256), losses := [] }

theorem u2409 : Upper (D 8) (R 8) [34,192,72,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2409 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2410 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 168 304 33 85 149 277), lower := (rows 35 194 76 168 304 33 64 128 256), losses := [] }

theorem u2410 : Upper (D 8) (R 8) [34,192,72,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2410 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2411 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 194 76 168 304 36 81 145 273), lower := (rows 35 194 76 168 304 36 64 128 256), losses := [] }

theorem u2411 : Upper (D 8) (R 8) [34,192,72,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2411 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2412 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 194 76 168 304 48 69 133 261), lower := (rows 35 194 76 168 304 48 64 128 256), losses := [] }

theorem u2412 : Upper (D 8) (R 8) [34,192,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2412 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2413 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 265 176 33 116 180 308), lower := (rows 35 194 76 265 176 33 64 128 256), losses := [] }

theorem u2413 : Upper (D 8) (R 8) [34,192,72,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2413 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2414 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 194 76 265 176 36 113 177 305), lower := (rows 35 194 76 265 176 36 64 128 256), losses := [] }

theorem u2414 : Upper (D 8) (R 8) [34,192,72,257,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2414 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2415 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 194 76 265 176 48 101 165 293), lower := (rows 35 194 76 265 176 48 64 128 256), losses := [] }

theorem u2415 : Upper (D 8) (R 8) [34,192,72,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2415 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2416 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 280 176 33 101 165 293), lower := (rows 35 194 76 280 176 33 64 128 256), losses := [] }

theorem u2416 : Upper (D 8) (R 8) [34,192,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2416 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2417 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 194 76 280 176 36 97 161 289), lower := (rows 35 194 76 280 176 36 64 128 256), losses := [] }

theorem u2417 : Upper (D 8) (R 8) [34,192,72,272,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2417 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2418 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 296 176 33 85 149 277), lower := (rows 35 194 76 296 176 33 64 128 256), losses := [] }

theorem u2418 : Upper (D 8) (R 8) [34,192,72,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2418 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2419 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 194 76 296 176 36 81 145 273), lower := (rows 35 194 76 296 176 36 64 128 256), losses := [] }

theorem u2419 : Upper (D 8) (R 8) [34,192,72,288,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2419 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2420 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 194 76 296 176 48 69 133 261), lower := (rows 35 194 76 296 176 48 64 128 256), losses := [] }

theorem u2420 : Upper (D 8) (R 8) [34,192,72,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2420 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2421 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 100 168 273 33 92 156 284), lower := (rows 35 194 100 168 273 33 64 128 256), losses := [] }

theorem u2421 : Upper (D 8) (R 8) [34,192,96,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2421 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2422 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 194 100 168 273 36 89 153 281), lower := (rows 35 194 100 168 273 36 64 128 256), losses := [] }

theorem u2422 : Upper (D 8) (R 8) [34,192,96,160,257,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2422 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2423 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 35 194 100 168 273 48 77 141 269), lower := (rows 35 194 100 168 273 48 64 128 256), losses := [] }

theorem u2423 : Upper (D 8) (R 8) [34,192,96,160,257,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2423 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2424 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 100 168 276 33 89 153 281), lower := (rows 35 194 100 168 276 33 64 128 256), losses := [] }

theorem u2424 : Upper (D 8) (R 8) [34,192,96,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2424 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2425 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 194 100 168 276 40 81 145 273), lower := (rows 35 194 100 168 276 40 64 128 256), losses := [] }

theorem u2425 : Upper (D 8) (R 8) [34,192,96,160,260,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2425 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2426 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 194 100 168 276 48 73 137 265), lower := (rows 35 194 100 168 276 48 64 128 256), losses := [] }

theorem u2426 : Upper (D 8) (R 8) [34,192,96,160,260,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2426 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2427 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 44 208 33 224 224 480), lower := (rows 35 259 28 44 208 33 64 128 256), losses := [] }

theorem u2427 : Upper (D 8) (R 8) [34,257,24,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2427 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2428 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 44, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 28 44 208 96 225 161 417), lower := (rows 35 259 28 44 208 96 64 128 256), losses := [] }

theorem u2428 : Upper (D 8) (R 8) [34,257,24,36,192,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2428 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2429 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 76 176 33 224 224 480), lower := (rows 35 259 28 76 176 33 64 128 256), losses := [] }

theorem u2429 : Upper (D 8) (R 8) [34,257,24,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2429 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2430 : PairBound 9 := { available := 161, camps := [{ cop := 5, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 76 176 96 225 161 417), lower := (rows 35 259 28 76 176 96 64 128 256), losses := [] }

theorem u2430 : Upper (D 8) (R 8) [34,257,24,68,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2430 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2431 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 28 76 176 160 97 225 353), lower := (rows 35 259 28 76 176 160 64 128 256), losses := [] }

theorem u2431 : Upper (D 8) (R 8) [34,257,24,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2431 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2432 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 104 176 33 196 196 452), lower := (rows 35 259 28 104 176 33 64 128 256), losses := [] }

theorem u2432 : Upper (D 8) (R 8) [34,257,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2433 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 259 28 104 176 36 193 193 449), lower := (rows 35 259 28 104 176 36 64 128 256), losses := [] }

theorem u2433 : Upper (D 8) (R 8) [34,257,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2433 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2434 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 28 104 176 96 197 133 389), lower := (rows 35 259 28 104 176 96 64 128 256), losses := [] }

theorem u2434 : Upper (D 8) (R 8) [34,257,24,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2434 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2435 : PairBound 9 := { available := 208, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 76 176 33 208 208 464), lower := (rows 35 259 44 76 176 33 64 128 256), losses := [] }

theorem u2435 : Upper (D 8) (R 8) [34,257,40,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2435 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2436 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 259 44 76 176 48 193 193 449), lower := (rows 35 259 44 76 176 48 64 128 256), losses := [] }

theorem u2436 : Upper (D 8) (R 8) [34,257,40,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2436 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2437 : PairBound 9 := { available := 145, camps := [{ cop := 5, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 259 44 76 176 96 209 145 401), lower := (rows 35 259 44 76 176 96 64 128 256), losses := [] }

theorem u2437 : Upper (D 8) (R 8) [34,257,40,68,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2437 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2438 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 44 76 176 160 81 209 337), lower := (rows 35 259 44 76 176 160 64 128 256), losses := [] }

theorem u2438 : Upper (D 8) (R 8) [34,257,40,68,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2438 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2439 : PairBound 9 := { available := 224, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 148 33 224 224 480), lower := (rows 35 259 44 88 148 33 64 128 256), losses := [] }

theorem u2439 : Upper (D 8) (R 8) [34,257,40,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2439 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2440 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 148 96 225 161 417), lower := (rows 35 259 44 88 148 96 64 128 256), losses := [] }

theorem u2440 : Upper (D 8) (R 8) [34,257,40,80,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2441 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 44 88 148 160 97 225 353), lower := (rows 35 259 44 88 148 160 64 128 256), losses := [] }

theorem u2441 : Upper (D 8) (R 8) [34,257,40,80,132,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2442 : PairBound 9 := { available := 196, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 176 33 196 196 452), lower := (rows 35 259 44 88 176 33 64 128 256), losses := [] }

theorem u2442 : Upper (D 8) (R 8) [34,257,40,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2442 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2443 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 259 44 88 176 36 193 193 449), lower := (rows 35 259 44 88 176 36 64 128 256), losses := [] }

theorem u2443 : Upper (D 8) (R 8) [34,257,40,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2443 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2444 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 88 176 96 197 133 389), lower := (rows 35 259 44 88 176 96 64 128 256), losses := [] }

theorem u2444 : Upper (D 8) (R 8) [34,257,40,80,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2445 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 44 88 176 160 69 197 325), lower := (rows 35 259 44 88 176 160 64 128 256), losses := [] }

theorem u2445 : Upper (D 8) (R 8) [34,257,40,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2446 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 44 200 112 33 212 148 404), lower := (rows 35 259 44 200 112 33 64 128 256), losses := [] }

theorem u2446 : Upper (D 8) (R 8) [34,257,40,192,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2447 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 259 44 200 112 36 209 145 401), lower := (rows 35 259 44 200 112 36 64 128 256), losses := [] }

theorem u2447 : Upper (D 8) (R 8) [34,257,40,192,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2447 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2448 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 259 44 200 112 48 197 133 389), lower := (rows 35 259 44 200 112 48 64 128 256), losses := [] }

theorem u2448 : Upper (D 8) (R 8) [34,257,40,192,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2448 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2449 : PairBound 9 := { available := 21, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 44 200 112 160 85 149 277), lower := (rows 35 259 44 200 112 160 64 128 256), losses := [] }

theorem u2449 : Upper (D 8) (R 8) [34,257,40,192,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2450 : PairBound 9 := { available := 148, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 168 112 33 212 148 404), lower := (rows 35 259 76 168 112 33 64 128 256), losses := [] }

theorem u2450 : Upper (D 8) (R 8) [34,257,72,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2451 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 259 76 168 112 36 209 145 401), lower := (rows 35 259 76 168 112 36 64 128 256), losses := [] }

theorem u2451 : Upper (D 8) (R 8) [34,257,72,160,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2451 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2452 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 35 259 76 168 112 48 197 133 389), lower := (rows 35 259 76 168 112 48 64 128 256), losses := [] }

theorem u2452 : Upper (D 8) (R 8) [34,257,72,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2452 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2453 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 76 168 112 160 85 149 277), lower := (rows 35 259 76 168 112 160 64 128 256), losses := [] }

theorem u2453 : Upper (D 8) (R 8) [34,257,72,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2454 : PairBound 9 := { available := 52, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 76 168 208 33 116 180 308), lower := (rows 35 259 76 168 208 33 64 128 256), losses := [] }

theorem u2454 : Upper (D 8) (R 8) [34,257,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2455 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 259 76 168 208 36 113 177 305), lower := (rows 35 259 76 168 208 36 64 128 256), losses := [] }

theorem u2455 : Upper (D 8) (R 8) [34,257,72,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2455 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2456 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 35 259 76 168 208 48 101 165 293), lower := (rows 35 259 76 168 208 48 64 128 256), losses := [] }

theorem u2456 : Upper (D 8) (R 8) [34,257,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2456 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2457 : PairBound 9 := { available := 28, camps := [{ cop := 8, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 259 100 168 208 33 92 156 284), lower := (rows 35 259 100 168 208 33 64 128 256), losses := [] }

theorem u2457 : Upper (D 8) (R 8) [34,257,96,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2458 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 35 259 100 168 208 36 89 153 281), lower := (rows 35 259 100 168 208 36 64 128 256), losses := [] }

theorem u2458 : Upper (D 8) (R 8) [34,257,96,160,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2458 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2459 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 35 259 100 168 208 48 77 141 269), lower := (rows 35 259 100 168 208 48 64 128 256), losses := [] }

theorem u2459 : Upper (D 8) (R 8) [34,257,96,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2459 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u2459
end Delivery.IrregularNine14.P08

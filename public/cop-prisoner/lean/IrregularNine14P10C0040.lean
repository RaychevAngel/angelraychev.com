import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0017

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2400 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 152 304 292 356 420 292), lower := (rows 67 131 76 152 304 32 64 128 256), losses := [] }

theorem u2400 : Upper (D 10) (R 10) [66,129,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2400 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2401 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 168 276 304 368 432 304), lower := (rows 67 131 76 168 276 32 64 128 256), losses := [] }

theorem u2401 : Upper (D 10) (R 10) [66,129,72,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2401 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2402 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 168 304 308 372 436 308), lower := (rows 67 131 76 168 304 32 64 128 256), losses := [] }

theorem u2402 : Upper (D 10) (R 10) [66,129,72,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2402 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2403 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 67 131 76 268 176 304 368 432 304), lower := (rows 67 131 76 268 176 32 64 128 256), losses := [] }

theorem u2403 : Upper (D 10) (R 10) [66,129,72,260,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2403 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2404 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 280 176 292 356 420 292), lower := (rows 67 131 76 280 176 32 64 128 256), losses := [] }

theorem u2404 : Upper (D 10) (R 10) [66,129,72,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2404 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2405 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 296 176 308 372 436 308), lower := (rows 67 131 76 296 176 32 64 128 256), losses := [] }

theorem u2405 : Upper (D 10) (R 10) [66,129,72,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2405 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2406 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 296 276 176 240 176 432), lower := (rows 67 131 76 296 276 32 64 128 256), losses := [] }

theorem u2406 : Upper (D 10) (R 10) [66,129,72,288,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2406 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2407 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 296 400 52 116 180 308), lower := (rows 67 131 76 296 400 32 64 128 256), losses := [] }

theorem u2407 : Upper (D 10) (R 10) [66,129,72,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2407 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2408 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 392 304 52 116 180 308), lower := (rows 67 131 76 392 304 32 64 128 256), losses := [] }

theorem u2408 : Upper (D 10) (R 10) [66,129,72,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2408 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2409 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 100 168 276 312 376 440 312), lower := (rows 67 131 100 168 276 32 64 128 256), losses := [] }

theorem u2409 : Upper (D 10) (R 10) [66,129,96,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2409 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2410 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 100 168 304 316 348 412 284), lower := (rows 67 131 100 168 304 32 64 128 256), losses := [] }

theorem u2410 : Upper (D 10) (R 10) [66,129,96,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2410 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2411 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 100 268 304 184 248 184 440), lower := (rows 67 131 100 268 304 32 64 128 256), losses := [] }

theorem u2411 : Upper (D 10) (R 10) [66,129,96,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2411 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2412 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 100 268 400 56 120 184 312), lower := (rows 67 131 100 268 400 32 64 128 256), losses := [] }

theorem u2412 : Upper (D 10) (R 10) [66,129,96,260,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2412 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2413 : PairBound 9 := { available := 60, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 100 296 400 60 124 188 316), lower := (rows 67 131 100 296 400 32 64 128 256), losses := [] }

theorem u2413 : Upper (D 10) (R 10) [66,129,96,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2413 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2414 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 3, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 67 131 196 268 304 56 120 184 312), lower := (rows 67 131 196 268 304 32 64 128 256), losses := [] }

theorem u2414 : Upper (D 10) (R 10) [66,129,192,260,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2414 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2415 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 152 273 288 352 416 288), lower := (rows 67 134 76 152 273 32 64 128 256), losses := [] }

theorem u2415 : Upper (D 10) (R 10) [66,132,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2415 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2416 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 152 304 289 353 417 289), lower := (rows 67 134 76 152 304 32 64 128 256), losses := [] }

theorem u2416 : Upper (D 10) (R 10) [66,132,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2416 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2417 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 168 273 304 368 432 304), lower := (rows 67 134 76 168 273 32 64 128 256), losses := [] }

theorem u2417 : Upper (D 10) (R 10) [66,132,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2417 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2418 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 168 304 305 369 433 305), lower := (rows 67 134 76 168 304 32 64 128 256), losses := [] }

theorem u2418 : Upper (D 10) (R 10) [66,132,72,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2418 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2419 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 265 176 304 368 432 304), lower := (rows 67 134 76 265 176 32 64 128 256), losses := [] }

theorem u2419 : Upper (D 10) (R 10) [66,132,72,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2419 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2420 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 265 400 48 112 176 304), lower := (rows 67 134 76 265 400 32 64 128 256), losses := [] }

theorem u2420 : Upper (D 10) (R 10) [66,132,72,257,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2420 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2421 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 280 176 289 353 417 289), lower := (rows 67 134 76 280 176 32 64 128 256), losses := [] }

theorem u2421 : Upper (D 10) (R 10) [66,132,72,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2421 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2422 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 296 176 305 369 433 305), lower := (rows 67 134 76 296 176 32 64 128 256), losses := [] }

theorem u2422 : Upper (D 10) (R 10) [66,132,72,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2422 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2423 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 296 273 176 240 176 432), lower := (rows 67 134 76 296 273 32 64 128 256), losses := [] }

theorem u2423 : Upper (D 10) (R 10) [66,132,72,288,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2423 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2424 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 296 400 49 113 177 305), lower := (rows 67 134 76 296 400 32 64 128 256), losses := [] }

theorem u2424 : Upper (D 10) (R 10) [66,132,72,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2424 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2425 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 392 273 48 112 176 304), lower := (rows 67 134 76 392 273 32 64 128 256), losses := [] }

theorem u2425 : Upper (D 10) (R 10) [66,132,72,384,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2425 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2426 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 76 392 304 49 113 177 305), lower := (rows 67 134 76 392 304 32 64 128 256), losses := [] }

theorem u2426 : Upper (D 10) (R 10) [66,132,72,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2426 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2427 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 152 273 296 360 424 296), lower := (rows 67 134 100 152 273 32 64 128 256), losses := [] }

theorem u2427 : Upper (D 10) (R 10) [66,132,96,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2427 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2428 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 152 304 297 361 425 297), lower := (rows 67 134 100 152 304 32 64 128 256), losses := [] }

theorem u2428 : Upper (D 10) (R 10) [66,132,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2428 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2429 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 168 273 312 376 440 312), lower := (rows 67 134 100 168 273 32 64 128 256), losses := [] }

theorem u2429 : Upper (D 10) (R 10) [66,132,96,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2429 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2430 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 168 280 305 369 433 305), lower := (rows 67 134 100 168 280 32 64 128 256), losses := [] }

theorem u2430 : Upper (D 10) (R 10) [66,132,96,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2430 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2431 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 168 304 313 345 409 281), lower := (rows 67 134 100 168 304 32 64 128 256), losses := [] }

theorem u2431 : Upper (D 10) (R 10) [66,132,96,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2431 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2432 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 265 304 184 248 184 440), lower := (rows 67 134 100 265 304 32 64 128 256), losses := [] }

theorem u2432 : Upper (D 10) (R 10) [66,132,96,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2432 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2433 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 265 400 56 120 184 312), lower := (rows 67 134 100 265 400 32 64 128 256), losses := [] }

theorem u2433 : Upper (D 10) (R 10) [66,132,96,257,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2433 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2434 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 100 296 400 57 121 185 313), lower := (rows 67 134 100 296 400 32 64 128 256), losses := [] }

theorem u2434 : Upper (D 10) (R 10) [66,132,96,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2434 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2435 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 3, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 67 134 196 265 304 56 120 184 312), lower := (rows 67 134 196 265 304 32 64 128 256), losses := [] }

theorem u2435 : Upper (D 10) (R 10) [66,132,192,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2435 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2436 : PairBound 9 := { available := 296, camps := [{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 328, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 67 134 261 88 176 296 360 424 296), lower := (rows 67 134 261 88 176 32 64 128 256), losses := [] }

theorem u2436 : Upper (D 10) (R 10) [66,132,257,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2436 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2437 : PairBound 9 := { available := 168, camps := [{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 200, targets := 256 }], pairs := [(3,8),(4,6)], upper := (rows 67 134 261 88 304 168 232 168 424), lower := (rows 67 134 261 88 304 32 64 128 256), losses := [] }

theorem u2437 : Upper (D 10) (R 10) [66,132,257,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2437 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2438 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 432, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 67 134 261 88 400 40 104 168 296), lower := (rows 67 134 261 88 400 32 64 128 256), losses := [] }

theorem u2438 : Upper (D 10) (R 10) [66,132,257,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2438 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2439 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 400, targets := 64 },{ cop := 4, region := 328, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 67 134 261 104 176 312 376 440 312), lower := (rows 67 134 261 104 176 32 64 128 256), losses := [] }

theorem u2439 : Upper (D 10) (R 10) [66,132,257,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2439 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2440 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 400, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(3,7),(4,6)], upper := (rows 67 134 261 104 400 56 120 184 312), lower := (rows 67 134 261 104 400 32 64 128 256), losses := [] }

theorem u2440 : Upper (D 10) (R 10) [66,132,257,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2440 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2441 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 1, region := 353, targets := 128 }], pairs := [(0,7),(4,6)], upper := (rows 67 134 268 88 176 289 353 417 289), lower := (rows 67 134 268 88 176 32 64 128 256), losses := [] }

theorem u2441 : Upper (D 10) (R 10) [66,132,264,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2441 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2442 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 227, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 134 268 88 400 33 97 161 289), lower := (rows 67 134 268 88 400 32 64 128 256), losses := [] }

theorem u2442 : Upper (D 10) (R 10) [66,132,264,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2442 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2443 : Route 9 := (fun mask => (mask,id))

def c2443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2443 : Upper (D 10) (R 10) [66,132,264,96,160] 13 := by
  apply FastRouting.sound _ _ [66,132,264,96,160] 13 (by decide) (choices 1) [1,16,256] r2443 c2443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1049
  · exact u1050
  · exact u1051

def r2444 : Route 9 := (fun mask => (mask,id))

def c2444 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2444 : Upper (D 10) (R 10) [66,132,264,96,288] 13 := by
  apply FastRouting.sound _ _ [66,132,264,96,288] 13 (by decide) (choices 1) [1,16,128] r2444 c2444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1052
  · exact u1053
  · exact u1054

def r2445 : Route 9 := (fun mask => (mask,id))

def c2445 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2445 : Upper (D 10) (R 10) [66,132,264,96,384] 13 := by
  apply FastRouting.sound _ _ [66,132,264,96,384] 13 (by decide) (choices 1) [1,16] r2445 c2445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1055
  · exact u1056

def b2446 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 369, targets := 128 }], pairs := [(0,7),(4,7)], upper := (rows 67 134 268 200 304 49 113 177 305), lower := (rows 67 134 268 200 304 32 64 128 256), losses := [] }

theorem u2446 : Upper (D 10) (R 10) [66,132,264,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2446 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2447 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 243, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 134 268 328 176 49 113 177 305), lower := (rows 67 134 268 328 176 32 64 128 256), losses := [] }

theorem u2447 : Upper (D 10) (R 10) [66,132,264,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2447 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2448 : Route 9 := (fun mask => (mask,id))

def c2448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2448 : Upper (D 10) (R 10) [66,132,288,80,160] 13 := by
  apply FastRouting.sound _ _ [66,132,288,80,160] 13 (by decide) (choices 1) [1,8,256] r2448 c2448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1057
  · exact u1058
  · exact u1059

def b2449 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 67 134 292 88 304 169 233 169 425), lower := (rows 67 134 292 88 304 32 64 128 256), losses := [] }

theorem u2449 : Upper (D 10) (R 10) [66,132,288,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2449 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2450 : Route 9 := (fun mask => (mask,id))

def c2450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2450 : Upper (D 10) (R 10) [66,132,288,80,384] 13 := by
  apply FastRouting.sound _ _ [66,132,288,80,384] 13 (by decide) (choices 1) [1,8] r2450 c2450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1060
  · exact u1061

def r2451 : Route 9 := (fun mask => (mask,id))

def c2451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2451 : Upper (D 10) (R 10) [66,132,288,96,136] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96,136] 13 (by decide) (choices 1) [1,16,256] r2451 c2451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1062
  · exact u1063
  · exact u1064

def r2452 : Route 9 := (fun mask => (mask,id))

def c2452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2452 : Upper (D 10) (R 10) [66,132,288,96,160] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96,160] 13 (by decide) (choices 1) [1,8,16,256] r2452 c2452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1065
  · exact u1066
  · exact u1067
  · exact u1068

def r2453 : Route 9 := (fun mask => (mask,id))

def c2453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2453 : Upper (D 10) (R 10) [66,132,288,96,264] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96,264] 13 (by decide) (choices 1) [1,16,128] r2453 c2453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1069
  · exact u1070
  · exact u1071

def b2454 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 67 134 292 104 304 185 217 153 409), lower := (rows 67 134 292 104 304 32 64 128 256), losses := [] }

theorem u2454 : Upper (D 10) (R 10) [66,132,288,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2454 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2455 : Route 9 := (fun mask => (mask,id))

def c2455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2455 : Upper (D 10) (R 10) [66,132,288,96,384] 13 := by
  apply FastRouting.sound _ _ [66,132,288,96,384] 13 (by decide) (choices 1) [1,8,16] r2455 c2455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1072
  · exact u1073
  · exact u1074

def b2456 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 67 134 292 152 304 105 105 233 361), lower := (rows 67 134 292 152 304 32 64 128 256), losses := [] }

theorem u2456 : Upper (D 10) (R 10) [66,132,288,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2456 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2457 : Route 9 := (fun mask => (mask,id))

def c2457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2457 : Upper (D 10) (R 10) [66,132,288,144,320] 13 := by
  apply FastRouting.sound _ _ [66,132,288,144,320] 13 (by decide) (choices 1) [1,8] r2457 c2457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1075
  · exact u1076

def r2458 : Route 9 := (fun mask => (mask,id))

def c2458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2458 : Upper (D 10) (R 10) [66,132,288,160,264] 13 := by
  apply FastRouting.sound _ _ [66,132,288,160,264] 13 (by decide) (choices 1) [1,16,64] r2458 c2458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1077
  · exact u1078
  · exact u1079

def b2459 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 67 134 292 168 304 121 89 217 345), lower := (rows 67 134 292 168 304 32 64 128 256), losses := [] }

theorem u2459 : Upper (D 10) (R 10) [66,132,288,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2459 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2459
end Delivery.IrregularNine14.P10

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

def b360 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 84 13 304 36 66 129 320), lower := (rows 11 162 84 13 304 36 66 129 256), losses := [] }

theorem u360 : Upper (D 6) (R 6) [10,160,80,5,288,4,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b360 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 13 304 36 66 192 257), lower := (rows 11 162 84 13 304 36 66 192 256), losses := [] }

theorem u361 : Upper (D 6) (R 6) [10,160,80,5,288,4,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b361 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 4, camps := [{ cop := 8, region := 235, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 162 84 296 22 96 65 129 260), lower := (rows 11 162 84 296 22 96 65 129 256), losses := [] }

theorem u362 : Upper (D 6) (R 6) [10,160,80,288,6,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 150, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 296 22 96 65 132 257), lower := (rows 11 162 84 296 22 96 65 132 256), losses := [] }

theorem u363 : Upper (D 6) (R 6) [10,160,80,288,6,64,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b363 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 348, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 162 84 328 52 33 66 129 260), lower := (rows 11 162 84 328 52 33 66 129 256), losses := [] }

theorem u364 : Upper (D 6) (R 6) [10,160,80,320,36,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b364 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 214, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 84 328 52 33 66 132 257), lower := (rows 11 162 84 328 52 33 66 132 256), losses := [] }

theorem u365 : Upper (D 6) (R 6) [10,160,80,320,36,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b365 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 5, region := 198, targets := 1 }], pairs := [(0,6),(1,0),(1,6)], upper := (rows 11 162 100 28 273 33 66 132 320), lower := (rows 11 162 100 28 273 33 66 132 256), losses := [] }

theorem u366 : Upper (D 6) (R 6) [10,160,96,20,257,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b366 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 5, region := 194, targets := 1 }], pairs := [(0,2),(1,0),(1,2)], upper := (rows 11 162 100 28 273 33 66 192 260), lower := (rows 11 162 100 28 273 33 66 192 256), losses := [] }

theorem u367 : Upper (D 6) (R 6) [10,160,96,20,257,1,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 280, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 162 100 88 276 33 66 129 260), lower := (rows 11 162 100 88 276 33 66 129 256), losses := [] }

theorem u368 : Upper (D 6) (R 6) [10,160,96,80,260,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 2, region := 130, targets := 64 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 162 100 88 276 33 66 132 257), lower := (rows 11 162 100 88 276 33 66 132 256), losses := [] }

theorem u369 : Upper (D 6) (R 6) [10,160,96,80,260,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 162 262 25 84 36 96 129 320), lower := (rows 11 162 262 25 84 36 96 129 256), losses := [] }

theorem u370 : Upper (D 6) (R 6) [10,160,258,17,68,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 262 25 84 36 96 192 257), lower := (rows 11 162 262 25 84 36 96 192 256), losses := [] }

theorem u371 : Upper (D 6) (R 6) [10,160,258,17,68,4,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 7, region := 358, targets := 1 }], pairs := [(0,6),(1,0),(1,6)], upper := (rows 11 162 262 28 81 36 96 129 320), lower := (rows 11 162 262 28 81 36 96 129 256), losses := [] }

theorem u372 : Upper (D 6) (R 6) [10,160,258,20,65,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b373 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 194, targets := 5 },{ cop := 0, region := 260, targets := 32 }], pairs := [(1,0),(1,2),(2,5)], upper := (rows 11 162 262 28 81 36 96 192 257), lower := (rows 11 162 262 28 81 36 96 192 256), losses := [] }

theorem u373 : Upper (D 6) (R 6) [10,160,258,20,65,4,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b373 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b374 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 163, targets := 68 }], pairs := [(0,2),(0,6),(1,2)], upper := (rows 11 162 262 28 112 33 68 129 320), lower := (rows 11 162 262 28 112 33 68 129 256), losses := [] }

theorem u374 : Upper (D 6) (R 6) [10,160,258,20,96,1,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b374 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 130, targets := 5 },{ cop := 0, region := 260, targets := 32 }], pairs := [(1,0),(1,2),(2,5)], upper := (rows 11 162 262 28 112 33 68 192 257), lower := (rows 11 162 262 28 112 33 68 192 256), losses := [] }

theorem u375 : Upper (D 6) (R 6) [10,160,258,20,96,1,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b376 : PairBound 9 := { available := 64, camps := [{ cop := 7, region := 358, targets := 1 },{ cop := 4, region := 104, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 162 262 88 21 36 96 129 320), lower := (rows 11 162 262 88 21 36 96 129 256), losses := [] }

theorem u376 : Upper (D 6) (R 6) [10,160,258,80,5,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b376 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b377 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 276, targets := 32 },{ cop := 0, region := 260, targets := 64 }], pairs := [(2,5),(2,6),(4,5)], upper := (rows 11 162 262 88 21 36 96 192 257), lower := (rows 11 162 262 88 21 36 96 192 256), losses := [] }

theorem u377 : Upper (D 6) (R 6) [10,160,258,80,5,4,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 32, camps := [{ cop := 7, region := 374, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 162 276 13 82 96 68 129 288), lower := (rows 11 162 276 13 82 96 68 129 256), losses := [] }

theorem u378 : Upper (D 6) (R 6) [10,160,272,5,66,64,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 349, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 162 276 13 82 96 68 160 257), lower := (rows 11 162 276 13 82 96 68 160 256), losses := [] }

theorem u379 : Upper (D 6) (R 6) [10,160,272,5,66,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b379 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 162 276 13 112 36 66 129 320), lower := (rows 11 162 276 13 112 36 66 129 256), losses := [] }

theorem u380 : Upper (D 6) (R 6) [10,160,272,5,96,4,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b380 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 210, targets := 5 }], pairs := [(1,0),(1,2),(4,0)], upper := (rows 11 162 276 13 112 36 66 192 257), lower := (rows 11 162 276 13 112 36 66 192 256), losses := [] }

theorem u381 : Upper (D 6) (R 6) [10,160,272,5,96,4,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b381 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b382 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 276, targets := 65 }], pairs := [(2,0),(2,6),(4,0)], upper := (rows 11 162 292 76 22 96 65 129 272), lower := (rows 11 162 292 76 22 96 65 129 256), losses := [] }

theorem u382 : Upper (D 6) (R 6) [10,160,288,68,6,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b382 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b383 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 146, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 11 162 292 76 22 96 65 144 257), lower := (rows 11 162 292 76 22 96 65 144 256), losses := [] }

theorem u383 : Upper (D 6) (R 6) [10,160,288,68,6,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b383 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 348, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 162 324 88 52 33 66 129 260), lower := (rows 11 162 324 88 52 33 66 129 256), losses := [] }

theorem u384 : Upper (D 6) (R 6) [10,160,320,80,36,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b384 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 202, targets := 1 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,0),(2,5),(3,0)], upper := (rows 11 162 324 88 52 33 66 132 257), lower := (rows 11 162 324 88 52 33 66 132 256), losses := [] }

theorem u385 : Upper (D 6) (R 6) [10,160,320,80,36,1,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b385 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,1),(4,0)], upper := (rows 25 35 69 138 274 96 96 132 260), lower := (rows 25 35 69 138 274 96 96 132 256), losses := [{ target := 0, region := (rows 0 2 4 8 24 511 511 132 388), good := (rows 120 98 484 506 370 96 96 484 352) }] }

theorem u386 : Upper (D 6) (R 6) [24,33,65,130,258,64,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b386 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 373, targets := 2 }], pairs := [(0,1),(2,1),(4,1)], upper := (rows 25 35 69 138 276 96 96 130 260), lower := (rows 25 35 69 138 276 96 96 130 256), losses := [] }

theorem u387 : Upper (D 6) (R 6) [24,33,65,130,260,64,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b387 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 98, targets := 4 }], pairs := [(1,2),(2,1),(3,2)], upper := (rows 25 35 69 138 276 96 96 132 258), lower := (rows 25 35 69 138 276 96 96 132 256), losses := [{ target := 2, region := (rows 1 7 0 136 16 511 511 128 415), good := (rows 379 355 355 490 370 96 96 490 352) }] }

theorem u388 : Upper (D 6) (R 6) [24,33,65,130,260,64,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b388 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 337, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 35 100 138 274 36 65 132 320), lower := (rows 25 35 100 138 274 36 65 132 256), losses := [] }

theorem u389 : Upper (D 6) (R 6) [24,33,96,130,258,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b389 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 201, targets := 36 }], pairs := [(0,2),(0,5),(3,2)], upper := (rows 25 35 100 138 274 36 65 192 260), lower := (rows 25 35 100 138 274 36 65 192 256), losses := [] }

theorem u390 : Upper (D 6) (R 6) [24,33,96,130,258,4,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b390 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 4, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 35 100 138 336 36 65 130 260), lower := (rows 25 35 100 138 336 36 65 130 256), losses := [] }

theorem u391 : Upper (D 6) (R 6) [24,33,96,130,320,4,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b391 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 337, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 35 100 138 336 36 65 132 258), lower := (rows 25 35 100 138 336 36 65 132 256), losses := [] }

theorem u392 : Upper (D 6) (R 6) [24,33,96,130,320,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b392 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 4, camps := [{ cop := 6, region := 308, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 35 100 138 336 36 66 129 260), lower := (rows 25 35 100 138 336 36 66 129 256), losses := [] }

theorem u393 : Upper (D 6) (R 6) [24,33,96,130,320,4,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b393 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 337, targets := 36 }], pairs := [(0,2),(0,5),(4,2)], upper := (rows 25 35 100 138 336 36 66 132 257), lower := (rows 25 35 100 138 336 36 66 132 256), losses := [] }

theorem u394 : Upper (D 6) (R 6) [24,33,96,130,320,4,2,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b394 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 140, targets := 96 }], pairs := [(2,5),(2,6),(3,5)], upper := (rows 25 35 133 14 276 96 96 130 320), lower := (rows 25 35 133 14 276 96 96 130 256), losses := [] }

theorem u395 : Upper (D 6) (R 6) [24,33,129,6,260,64,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b395 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 273, targets := 96 }], pairs := [(0,5),(0,6),(4,5)], upper := (rows 25 35 133 14 276 96 96 192 258), lower := (rows 25 35 133 14 276 96 96 192 256), losses := [] }

theorem u396 : Upper (D 6) (R 6) [24,33,129,6,260,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b396 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 273, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 35 133 76 276 34 96 130 320), lower := (rows 25 35 133 76 276 34 96 130 256), losses := [] }

theorem u397 : Upper (D 6) (R 6) [24,33,129,68,260,2,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b397 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 307, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 25 35 133 76 276 34 96 192 258), lower := (rows 25 35 133 76 276 34 96 192 256), losses := [] }

theorem u398 : Upper (D 6) (R 6) [24,33,129,68,260,2,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b398 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b399 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 3, region := 132, targets := 32 }], pairs := [(1,0),(2,5),(4,0)], upper := (rows 25 38 133 11 276 96 96 130 320), lower := (rows 25 38 133 11 276 96 96 130 256), losses := [] }

theorem u399 : Upper (D 6) (R 6) [24,36,129,3,260,64,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b399 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 133 11 276 96 96 192 258), lower := (rows 25 38 133 11 276 96 96 192 256), losses := [] }

theorem u400 : Upper (D 6) (R 6) [24,36,129,3,260,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b400 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 32, camps := [{ cop := 7, region := 358, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 25 38 134 11 84 96 320 129 288), lower := (rows 25 38 134 11 84 96 320 129 256), losses := [] }

theorem u401 : Upper (D 6) (R 6) [24,36,130,3,68,64,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b401 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 6, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 25 38 134 11 84 96 320 160 257), lower := (rows 25 38 134 11 84 96 320 160 256), losses := [] }

theorem u402 : Upper (D 6) (R 6) [24,36,130,3,68,64,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b402 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 64, camps := [{ cop := 7, region := 374, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 38 134 11 276 96 96 129 320), lower := (rows 25 38 134 11 276 96 96 129 256), losses := [] }

theorem u403 : Upper (D 6) (R 6) [24,36,130,3,260,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b403 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b404 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 134 11 276 96 96 192 257), lower := (rows 25 38 134 11 276 96 96 192 256), losses := [] }

theorem u404 : Upper (D 6) (R 6) [24,36,130,3,260,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b404 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b405 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 141, targets := 96 }], pairs := [(0,5),(0,6)], upper := (rows 25 38 134 13 82 96 320 129 288), lower := (rows 25 38 134 13 82 96 320 129 256), losses := [] }

theorem u405 : Upper (D 6) (R 6) [24,36,130,5,66,64,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b405 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 6, targets := 65 }], pairs := [(1,0),(1,6)], upper := (rows 25 38 134 13 82 96 320 160 257), lower := (rows 25 38 134 13 82 96 320 160 256), losses := [] }

theorem u406 : Upper (D 6) (R 6) [24,36,130,5,66,64,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b406 [(6,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 141, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 25 38 134 13 274 96 96 129 320), lower := (rows 25 38 134 13 274 96 96 129 256), losses := [] }

theorem u407 : Upper (D 6) (R 6) [24,36,130,5,258,64,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b407 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 281, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 25 38 134 13 274 96 96 192 257), lower := (rows 25 38 134 13 274 96 96 192 256), losses := [] }

theorem u408 : Upper (D 6) (R 6) [24,36,130,5,258,64,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b408 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b409 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 1, region := 272, targets := 2 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 25 38 134 74 276 96 65 129 288), lower := (rows 25 38 134 74 276 96 65 129 256), losses := [] }

theorem u409 : Upper (D 6) (R 6) [24,36,130,66,260,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b409 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b410 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 74 276 96 65 160 257), lower := (rows 25 38 134 74 276 96 65 160 256), losses := [] }

theorem u410 : Upper (D 6) (R 6) [24,36,130,66,260,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b410 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b411 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 38 134 76 274 96 65 129 288), lower := (rows 25 38 134 76 274 96 65 129 256), losses := [] }

theorem u411 : Upper (D 6) (R 6) [24,36,130,68,258,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b411 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b412 : PairBound 9 := { available := 1, camps := [{ cop := 7, region := 6, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 25 38 134 76 274 96 65 160 257), lower := (rows 25 38 134 76 274 96 65 160 256), losses := [] }

theorem u412 : Upper (D 6) (R 6) [24,36,130,68,258,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b412 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b413 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 25 38 134 76 304 96 65 129 258), lower := (rows 25 38 134 76 304 96 65 129 256), losses := [] }

theorem u413 : Upper (D 6) (R 6) [24,36,130,68,288,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b413 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b414 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 305, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 25 38 134 76 304 96 65 130 257), lower := (rows 25 38 134 76 304 96 65 130 256), losses := [] }

theorem u414 : Upper (D 6) (R 6) [24,36,130,68,288,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b414 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b415 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 344, targets := 1 },{ cop := 1, region := 72, targets := 4 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 25 38 196 104 276 33 66 129 258), lower := (rows 25 38 196 104 276 33 66 129 256), losses := [] }

theorem u415 : Upper (D 6) (R 6) [24,36,192,96,260,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b415 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 313, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 38 196 104 276 33 66 130 257), lower := (rows 25 38 196 104 276 33 66 130 256), losses := [] }

theorem u416 : Upper (D 6) (R 6) [24,36,192,96,260,1,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b416 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 337, targets := 34 }], pairs := [(0,1),(0,5),(4,1)], upper := (rows 25 98 133 44 276 34 65 130 320), lower := (rows 25 98 133 44 276 34 65 130 256), losses := [] }

theorem u417 : Upper (D 6) (R 6) [24,96,129,36,260,2,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b417 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b418 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 196, targets := 34 },{ cop := 6, region := 34, targets := 1 }], pairs := [(1,0),(2,1),(2,5)], upper := (rows 25 98 133 44 276 34 65 192 258), lower := (rows 25 98 133 44 276 34 65 192 256), losses := [] }

theorem u418 : Upper (D 6) (R 6) [24,96,129,36,260,2,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b418 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b419 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 272, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 25 98 134 44 274 33 68 129 320), lower := (rows 25 98 134 44 274 33 68 129 256), losses := [] }

theorem u419 : Upper (D 6) (R 6) [24,96,130,36,258,1,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b419 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P06

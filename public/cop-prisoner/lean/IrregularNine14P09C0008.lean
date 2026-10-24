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

def b480 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5),(4,5)], upper := (rows 7 42 100 152 336 33 192 385 257), lower := (rows 7 42 100 152 336 33 192 128 256), losses := [] }

theorem u480 : Upper (D 9) (R 9) [6,40,96,144,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b480 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b481 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 100 152 336 33 320 129 385), lower := (rows 7 42 100 152 336 33 320 128 256), losses := [] }

theorem u481 : Upper (D 9) (R 9) [6,40,96,144,320,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b481 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b482 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 69, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,5)], upper := (rows 7 42 100 200 145 288 65 400 272), lower := (rows 7 42 100 200 145 288 65 128 256), losses := [] }

theorem u482 : Upper (D 9) (R 9) [6,40,96,192,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b482 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 200 145 288 80 385 257), lower := (rows 7 42 100 200 145 288 80 128 256), losses := [] }

theorem u483 : Upper (D 9) (R 9) [6,40,96,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b483 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 155, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,8)], upper := (rows 7 42 100 200 145 288 320 145 273), lower := (rows 7 42 100 200 145 288 320 128 256), losses := [] }

theorem u484 : Upper (D 9) (R 9) [6,40,96,192,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b484 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b485 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 69, targets := 384 }], pairs := [(0,7),(0,8),(2,7),(2,8)], upper := (rows 7 42 100 200 273 48 65 384 384), lower := (rows 7 42 100 200 273 48 65 128 256), losses := [] }

theorem u485 : Upper (D 9) (R 9) [6,40,96,192,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b485 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b486 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 100 200 273 48 192 385 257), lower := (rows 7 42 100 200 273 48 192 128 256), losses := [] }

theorem u486 : Upper (D 9) (R 9) [6,40,96,192,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b486 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b487 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 0, region := 456, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 7 42 100 200 273 48 320 129 385), lower := (rows 7 42 100 200 273 48 320 128 256), losses := [] }

theorem u487 : Upper (D 9) (R 9) [6,40,96,192,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b487 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b488 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 69, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,5)], upper := (rows 7 42 100 200 273 288 65 144 400), lower := (rows 7 42 100 200 273 288 65 128 256), losses := [] }

theorem u488 : Upper (D 9) (R 9) [6,40,96,192,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b488 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b489 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8)], upper := (rows 7 42 100 200 273 288 80 129 385), lower := (rows 7 42 100 200 273 288 80 128 256), losses := [] }

theorem u489 : Upper (D 9) (R 9) [6,40,96,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b489 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 7 42 100 200 273 288 192 145 273), lower := (rows 7 42 100 200 273 288 192 128 256), losses := [] }

theorem u490 : Upper (D 9) (R 9) [6,40,96,192,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b490 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 384 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,5)], upper := (rows 7 42 100 200 400 288 65 145 273), lower := (rows 7 42 100 200 400 288 65 128 256), losses := [] }

theorem u491 : Upper (D 9) (R 9) [6,40,96,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b491 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 139, targets := 256 },{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8)], upper := (rows 7 42 100 200 400 288 80 129 257), lower := (rows 7 42 100 200 400 288 80 128 256), losses := [] }

theorem u492 : Upper (D 9) (R 9) [6,40,96,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b492 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 42 100 392 145 33 80 448 320), lower := (rows 7 42 100 392 145 33 80 128 256), losses := [] }

theorem u493 : Upper (D 9) (R 9) [6,40,96,384,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b493 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 392 145 33 320 208 336), lower := (rows 7 42 100 392 145 33 320 128 256), losses := [] }

theorem u494 : Upper (D 9) (R 9) [6,40,96,384,129,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b494 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 69, targets := 384 },{ cop := 6, region := 408, targets := 1 }], pairs := [(0,7),(0,8),(2,7),(2,8),(3,0)], upper := (rows 7 42 100 392 208 33 65 400 272), lower := (rows 7 42 100 392 208 33 65 128 256), losses := [] }

theorem u495 : Upper (D 9) (R 9) [6,40,96,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b495 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b496 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 7 42 100 392 208 33 80 385 257), lower := (rows 7 42 100 392 208 33 80 128 256), losses := [] }

theorem u496 : Upper (D 9) (R 9) [6,40,96,384,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b496 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b497 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 392 208 33 320 145 273), lower := (rows 7 42 100 392 208 33 320 128 256), losses := [] }

theorem u497 : Upper (D 9) (R 9) [6,40,96,384,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b497 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 418, targets := 65 },{ cop := 6, region := 388, targets := 1 }], pairs := [(0,5),(1,0),(1,6),(2,0),(2,5)], upper := (rows 7 42 196 25 112 288 65 384 384), lower := (rows 7 42 196 25 112 288 65 128 256), losses := [] }

theorem u498 : Upper (D 9) (R 9) [6,40,192,17,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b498 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 42 196 25 112 288 192 385 257), lower := (rows 7 42 196 25 112 288 192 128 256), losses := [] }

theorem u499 : Upper (D 9) (R 9) [6,40,192,17,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b499 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 42 196 25 112 288 320 129 385), lower := (rows 7 42 196 25 112 288 320 128 256), losses := [] }

theorem u500 : Upper (D 9) (R 9) [6,40,192,17,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b500 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b501 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 98, targets := 128 }], pairs := [(0,5),(1,7),(2,5),(4,0),(4,6)], upper := (rows 7 42 196 25 304 96 65 384 384), lower := (rows 7 42 196 25 304 96 65 128 256), losses := [] }

theorem u501 : Upper (D 9) (R 9) [6,40,192,17,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b501 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b502 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 25 304 96 192 385 257), lower := (rows 7 42 196 25 304 96 192 128 256), losses := [] }

theorem u502 : Upper (D 9) (R 9) [6,40,192,17,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b502 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 6, region := 48, targets := 129 }], pairs := [(0,5),(1,0),(2,5),(4,0),(4,7)], upper := (rows 7 42 196 25 304 96 320 129 385), lower := (rows 7 42 196 25 304 96 320 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 336 380 336 128 256), good := (rows 38 42 244 122 368 112 368 128 368) }] }

theorem u503 : Upper (D 9) (R 9) [6,40,192,17,288,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b503 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 418, targets := 65 },{ cop := 6, region := 436, targets := 1 }], pairs := [(1,0),(1,6),(2,0),(3,7),(4,0)], upper := (rows 7 42 196 25 336 160 65 416 288), lower := (rows 7 42 196 25 336 160 65 128 256), losses := [{ target := 7, region := (rows 1 2 4 73 19 32 73 0 290), good := (rows 351 378 76 89 344 288 89 0 256) }] }

theorem u504 : Upper (D 9) (R 9) [6,40,192,17,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b504 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 68, targets := 257 },{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6),(2,0),(2,8),(3,7),(4,7)], upper := (rows 7 42 196 25 336 160 96 385 257), lower := (rows 7 42 196 25 336 160 96 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 19 32 98 0 265), good := (rows 351 378 68 281 336 96 96 0 256) }] }

theorem u505 : Upper (D 9) (R 9) [6,40,192,17,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b505 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 175, targets := 256 },{ cop := 6, region := 16, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 196 25 336 160 320 161 289), lower := (rows 7 42 196 25 336 160 320 128 256), losses := [] }

theorem u506 : Upper (D 9) (R 9) [6,40,192,17,320,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b506 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 3, region := 434, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(3,8)], upper := (rows 7 42 196 73 176 288 65 400 272), lower := (rows 7 42 196 73 176 288 65 128 256), losses := [] }

theorem u507 : Upper (D 9) (R 9) [6,40,192,65,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b507 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b508 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 42 196 73 176 288 80 385 257), lower := (rows 7 42 196 73 176 288 80 128 256), losses := [] }

theorem u508 : Upper (D 9) (R 9) [6,40,192,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b508 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b509 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(2,0),(4,0),(4,6)], upper := (rows 7 42 196 73 176 288 320 145 273), lower := (rows 7 42 196 73 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 20 352 352 128 256), good := (rows 22 106 244 106 244 352 352 128 352) }] }

theorem u509 : Upper (D 9) (R 9) [6,40,192,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b509 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b510 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 106, targets := 384 }], pairs := [(1,7),(1,8),(3,7),(3,8)], upper := (rows 7 42 196 73 273 48 96 384 384), lower := (rows 7 42 196 73 273 48 96 128 256), losses := [] }

theorem u510 : Upper (D 9) (R 9) [6,40,192,65,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b510 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b511 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 73 273 48 192 416 288), lower := (rows 7 42 196 73 273 48 192 128 256), losses := [] }

theorem u511 : Upper (D 9) (R 9) [6,40,192,65,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b511 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b512 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,6),(1,7),(3,7),(4,6)], upper := (rows 7 42 196 73 273 48 320 160 416), lower := (rows 7 42 196 73 273 48 320 128 256), losses := [] }

theorem u512 : Upper (D 9) (R 9) [6,40,192,65,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b512 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b513 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,0),(1,6),(2,0),(4,6)], upper := (rows 7 42 196 73 273 288 80 160 416), lower := (rows 7 42 196 73 273 288 80 128 256), losses := [] }

theorem u513 : Upper (D 9) (R 9) [6,40,192,65,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b513 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b514 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 404, targets := 32 },{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,6),(1,7),(2,5),(4,5),(4,6)], upper := (rows 7 42 196 73 273 288 96 144 400), lower := (rows 7 42 196 73 273 288 96 128 256), losses := [] }

theorem u514 : Upper (D 9) (R 9) [6,40,192,65,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b514 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b515 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 42 196 73 273 288 192 176 304), lower := (rows 7 42 196 73 273 288 192 128 256), losses := [] }

theorem u515 : Upper (D 9) (R 9) [6,40,192,65,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b515 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b516 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 42 196 73 400 48 65 416 288), lower := (rows 7 42 196 73 400 48 65 128 256), losses := [] }

theorem u516 : Upper (D 9) (R 9) [6,40,192,65,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b516 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b517 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 42 196 73 400 48 96 385 257), lower := (rows 7 42 196 73 400 48 96 128 256), losses := [] }

theorem u517 : Upper (D 9) (R 9) [6,40,192,65,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b517 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b518 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 68, targets := 1 },{ cop := 4, region := 68, targets := 32 }], pairs := [(1,6),(2,0),(2,5),(4,6)], upper := (rows 7 42 196 73 400 48 320 161 289), lower := (rows 7 42 196 73 400 48 320 128 256), losses := [] }

theorem u518 : Upper (D 9) (R 9) [6,40,192,65,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b518 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b519 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 416 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(3,7),(3,8)], upper := (rows 7 42 196 73 400 288 65 176 304), lower := (rows 7 42 196 73 400 288 65 128 256), losses := [] }

theorem u519 : Upper (D 9) (R 9) [6,40,192,65,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b519 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b520 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 3, region := 290, targets := 64 }], pairs := [(0,7),(1,6),(1,7),(3,7)], upper := (rows 7 42 196 73 400 288 80 161 289), lower := (rows 7 42 196 73 400 288 80 128 256), losses := [] }

theorem u520 : Upper (D 9) (R 9) [6,40,192,65,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b520 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b521 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 404, targets := 32 },{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 100, targets := 1 }], pairs := [(1,6),(2,0),(2,5),(4,5),(4,6)], upper := (rows 7 42 196 73 400 288 96 145 273), lower := (rows 7 42 196 73 400 288 96 128 256), losses := [] }

theorem u521 : Upper (D 9) (R 9) [6,40,192,65,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b521 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b522 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 76, targets := 288 },{ cop := 3, region := 290, targets := 1 }], pairs := [(1,0),(2,5),(2,8),(3,5),(3,8)], upper := (rows 7 42 196 88 145 288 65 416 288), lower := (rows 7 42 196 88 145 288 65 128 256), losses := [] }

theorem u522 : Upper (D 9) (R 9) [6,40,192,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b522 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b523 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(0,5),(1,7),(3,7),(4,5),(4,6)], upper := (rows 7 42 196 88 145 288 96 385 257), lower := (rows 7 42 196 88 145 288 96 128 256), losses := [{ target := 5, region := (rows 3 2 12 8 19 0 64 147 275), good := (rows 407 415 196 476 401 256 64 128 256) }] }

theorem u523 : Upper (D 9) (R 9) [6,40,192,80,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b523 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(3,7),(4,6)], upper := (rows 7 42 196 88 145 288 320 161 289), lower := (rows 7 42 196 88 145 288 320 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 352 352 128 256), good := (rows 6 106 228 122 144 352 352 128 352) },{ target := 6, region := (rows 1 10 4 8 17 377 0 145 273), good := (rows 439 42 164 442 433 288 288 128 288) }] }

theorem u524 : Upper (D 9) (R 9) [6,40,192,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b524 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b525 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 42 196 88 176 288 65 385 257), lower := (rows 7 42 196 88 176 288 65 128 256), losses := [] }

theorem u525 : Upper (D 9) (R 9) [6,40,192,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b525 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b526 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,5),(1,0),(2,0),(2,5),(4,6)], upper := (rows 7 42 196 88 176 288 320 129 257), lower := (rows 7 42 196 88 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 30 20 28 20 352 352 128 256), good := (rows 30 106 254 126 254 352 352 128 352) }] }

theorem u526 : Upper (D 9) (R 9) [6,40,192,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b526 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 72, targets := 416 },{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(3,7),(3,8)], upper := (rows 7 42 196 88 273 160 65 416 288), lower := (rows 7 42 196 88 273 160 65 128 256), losses := [] }

theorem u527 : Upper (D 9) (R 9) [6,40,192,80,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b527 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 257, camps := [{ cop := 5, region := 68, targets := 257 },{ cop := 0, region := 272, targets := 32 },{ cop := 0, region := 272, targets := 64 },{ cop := 0, region := 272, targets := 128 }], pairs := [(2,0),(2,8),(4,5),(4,6),(4,7)], upper := (rows 7 42 196 88 273 160 96 385 257), lower := (rows 7 42 196 88 273 160 96 128 256), losses := [] }

theorem u528 : Upper (D 9) (R 9) [6,40,192,80,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b528 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 33 }], pairs := [(0,8),(1,8),(2,8),(3,0),(3,5)], upper := (rows 7 42 196 88 273 160 320 161 289), lower := (rows 7 42 196 88 273 160 320 128 256), losses := [] }

theorem u529 : Upper (D 9) (R 9) [6,40,192,80,257,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b529 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 388, targets := 1 }], pairs := [(0,5),(2,0),(2,5),(4,0),(4,6)], upper := (rows 7 42 196 88 304 33 65 384 384), lower := (rows 7 42 196 88 304 33 65 128 256), losses := [] }

theorem u530 : Upper (D 9) (R 9) [6,40,192,80,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b530 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b531 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 42 196 88 304 33 192 385 257), lower := (rows 7 42 196 88 304 33 192 128 256), losses := [] }

theorem u531 : Upper (D 9) (R 9) [6,40,192,80,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b531 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b532 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 74, targets := 129 },{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 196 88 304 33 320 129 385), lower := (rows 7 42 196 88 304 33 320 128 256), losses := [] }

theorem u532 : Upper (D 9) (R 9) [6,40,192,80,288,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b532 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r533 : Route 9 := (fun mask => (mask,id))

def c533 : Nat → Fin 9 := (fun mask => match mask with | 1 => 8 | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | _ => 0)

theorem u533 : Upper (D 9) (R 9) [6,40,192,80,288,128,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,80,288,128,1] 13 (by decide) (choices 1) [256] r533 c533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u24

def b534 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 74, targets := 129 },{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 196 88 304 160 320 129 257), lower := (rows 7 42 196 88 304 160 320 128 256), losses := [] }

theorem u534 : Upper (D 9) (R 9) [6,40,192,80,288,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b534 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b535 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 7 42 196 88 400 33 65 416 288), lower := (rows 7 42 196 88 400 33 65 128 256), losses := [] }

theorem u535 : Upper (D 9) (R 9) [6,40,192,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b535 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b536 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,5)], upper := (rows 7 42 196 88 400 33 96 385 257), lower := (rows 7 42 196 88 400 33 96 128 256), losses := [] }

theorem u536 : Upper (D 9) (R 9) [6,40,192,80,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b536 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 33 },{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(2,0),(2,5),(3,0),(3,5)], upper := (rows 7 42 196 88 400 33 320 161 289), lower := (rows 7 42 196 88 400 33 320 128 256), losses := [] }

theorem u537 : Upper (D 9) (R 9) [6,40,192,80,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b537 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b538 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 114, targets := 384 }], pairs := [(1,7),(1,8),(4,7),(4,8)], upper := (rows 7 42 196 265 81 48 96 384 384), lower := (rows 7 42 196 265 81 48 96 128 256), losses := [] }

theorem u538 : Upper (D 9) (R 9) [6,40,192,257,65,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b538 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 265 81 48 192 416 288), lower := (rows 7 42 196 265 81 48 192 128 256), losses := [] }

theorem u539 : Upper (D 9) (R 9) [6,40,192,257,65,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b539 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P09

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

def b360 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 88, targets := 384 }], pairs := [(3,7),(3,8),(4,7),(4,8)], upper := (rows 7 35 196 25 112 288 72 384 384), lower := (rows 7 35 196 25 112 288 72 128 256), losses := [] }

theorem u360 : Upper (D 9) (R 9) [6,33,192,17,96,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b360 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 35 196 25 112 288 192 392 264), lower := (rows 7 35 196 25 112 288 192 128 256), losses := [] }

theorem u361 : Upper (D 9) (R 9) [6,33,192,17,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b361 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 3, region := 452, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 35 196 25 112 288 320 136 392), lower := (rows 7 35 196 25 112 288 320 128 256), losses := [] }

theorem u362 : Upper (D 9) (R 9) [6,33,192,17,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b362 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 3, region := 500, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 35 196 25 336 288 72 160 416), lower := (rows 7 35 196 25 336 288 72 128 256), losses := [] }

theorem u363 : Upper (D 9) (R 9) [6,33,192,17,320,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b363 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 500, targets := 1 },{ cop := 3, region := 418, targets := 64 },{ cop := 5, region := 80, targets := 128 }], pairs := [(1,6),(1,7),(2,0),(4,0),(4,7)], upper := (rows 7 35 196 25 336 288 96 136 392), lower := (rows 7 35 196 25 336 288 96 128 256), losses := [{ target := 7, region := (rows 1 10 4 10 304 304 378 0 256), good := (rows 79 123 68 123 368 368 112 0 368) }] }

theorem u364 : Upper (D 9) (R 9) [6,33,192,17,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b364 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 35 196 25 336 288 192 168 296), lower := (rows 7 35 196 25 336 288 192 128 256), losses := [] }

theorem u365 : Upper (D 9) (R 9) [6,33,192,17,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b365 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 384, camps := [{ cop := 1, region := 88, targets := 384 },{ cop := 6, region := 388, targets := 1 }], pairs := [(2,0),(3,7),(3,8),(4,7),(4,8)], upper := (rows 7 35 196 56 88 288 65 384 384), lower := (rows 7 35 196 56 88 288 65 128 256), losses := [] }

theorem u366 : Upper (D 9) (R 9) [6,33,192,48,72,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b366 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 35 196 56 88 288 192 385 257), lower := (rows 7 35 196 56 88 288 192 128 256), losses := [] }

theorem u367 : Upper (D 9) (R 9) [6,33,192,48,72,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b367 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 88, targets := 129 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 35 196 56 88 288 320 129 385), lower := (rows 7 35 196 56 88 288 320 128 256), losses := [] }

theorem u368 : Upper (D 9) (R 9) [6,33,192,48,72,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b368 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6),(0,7),(1,7),(3,7)], upper := (rows 7 35 196 73 152 288 80 416 288), lower := (rows 7 35 196 73 152 288 80 128 256), losses := [] }

theorem u369 : Upper (D 9) (R 9) [6,33,192,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b369 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 72, targets := 384 },{ cop := 3, region := 404, targets := 1 },{ cop := 3, region := 404, targets := 32 }], pairs := [(2,0),(2,5),(3,7),(3,8),(4,0)], upper := (rows 7 35 196 73 152 288 96 400 272), lower := (rows 7 35 196 73 152 288 96 128 256), losses := [] }

theorem u370 : Upper (D 9) (R 9) [6,33,192,65,136,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b370 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,0),(3,5),(4,0),(4,6)], upper := (rows 7 35 196 73 152 288 320 176 304), lower := (rows 7 35 196 73 152 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 4 10 16 0 352 128 256), good := (rows 15 75 196 73 152 320 320 128 320) }] }

theorem u371 : Upper (D 9) (R 9) [6,33,192,65,136,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b371 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 272, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 196 73 176 288 72 400 272), lower := (rows 7 35 196 73 176 288 72 128 256), losses := [] }

theorem u372 : Upper (D 9) (R 9) [6,33,192,65,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b372 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b373 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 196 73 176 288 80 392 264), lower := (rows 7 35 196 73 176 288 80 128 256), losses := [] }

theorem u373 : Upper (D 9) (R 9) [6,33,192,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b373 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b374 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 1 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,0),(2,5),(4,0),(4,6)], upper := (rows 7 35 196 73 176 288 320 152 280), lower := (rows 7 35 196 73 176 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 20 10 16 0 352 128 256), good := (rows 15 75 196 73 212 320 320 128 320) }] }

theorem u374 : Upper (D 9) (R 9) [6,33,192,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b374 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 291, targets := 64 },{ cop := 3, region := 436, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,0)], upper := (rows 7 35 196 73 280 288 80 160 416), lower := (rows 7 35 196 73 280 288 80 128 256), losses := [] }

theorem u375 : Upper (D 9) (R 9) [6,33,192,65,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b375 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b376 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 72, targets := 384 },{ cop := 3, region := 404, targets := 1 },{ cop := 3, region := 404, targets := 32 }], pairs := [(2,0),(2,5),(3,7),(3,8),(4,0)], upper := (rows 7 35 196 73 280 288 96 144 400), lower := (rows 7 35 196 73 280 288 96 128 256), losses := [] }

theorem u376 : Upper (D 9) (R 9) [6,33,192,65,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b376 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b377 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 35 196 73 280 288 192 176 304), lower := (rows 7 35 196 73 280 288 192 128 256), losses := [] }

theorem u377 : Upper (D 9) (R 9) [6,33,192,65,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b377 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 416 },{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(3,5),(3,7),(3,8)], upper := (rows 7 35 196 73 400 288 72 176 304), lower := (rows 7 35 196 73 400 288 72 128 256), losses := [] }

theorem u378 : Upper (D 9) (R 9) [6,33,192,65,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b378 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 3, region := 420, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 35 196 73 400 288 80 168 296), lower := (rows 7 35 196 73 400 288 80 128 256), losses := [] }

theorem u379 : Upper (D 9) (R 9) [6,33,192,65,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b379 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 72, targets := 384 },{ cop := 3, region := 404, targets := 1 },{ cop := 3, region := 404, targets := 32 }], pairs := [(2,0),(2,5),(3,7),(3,8),(4,0)], upper := (rows 7 35 196 73 400 288 96 152 280), lower := (rows 7 35 196 73 400 288 96 128 256), losses := [] }

theorem u380 : Upper (D 9) (R 9) [6,33,192,65,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b380 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 6, region := 444, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 35 196 88 176 288 65 392 264), lower := (rows 7 35 196 88 176 288 65 128 256), losses := [] }

theorem u381 : Upper (D 9) (R 9) [6,33,192,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b381 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b382 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 76, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 7 35 196 88 176 288 72 385 257), lower := (rows 7 35 196 88 176 288 72 128 256), losses := [] }

theorem u382 : Upper (D 9) (R 9) [6,33,192,80,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b382 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b383 : PairBound 9 := { available := 9, camps := [], pairs := [(2,0),(2,5),(3,0),(3,5),(4,0)], upper := (rows 7 35 196 88 176 288 320 137 265), lower := (rows 7 35 196 88 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 20 28 20 352 352 128 256), good := (rows 30 98 252 124 252 352 352 128 352) },{ target := 5, region := (rows 1 2 20 24 16 0 352 128 256), good := (rows 7 67 196 92 220 320 320 128 320) }] }

theorem u383 : Upper (D 9) (R 9) [6,33,192,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b383 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 106, targets := 384 }], pairs := [(1,7),(1,8),(3,7),(3,8)], upper := (rows 7 35 196 88 273 40 96 384 384), lower := (rows 7 35 196 88 273 40 96 128 256), losses := [] }

theorem u384 : Upper (D 9) (R 9) [6,33,192,80,257,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b384 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 196 88 273 40 192 416 288), lower := (rows 7 35 196 88 273 40 192 128 256), losses := [] }

theorem u385 : Upper (D 9) (R 9) [6,33,192,80,257,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b385 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 7 35 196 88 273 40 320 160 416), lower := (rows 7 35 196 88 273 40 320 128 256), losses := [] }

theorem u386 : Upper (D 9) (R 9) [6,33,192,80,257,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b386 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 307, targets := 64 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 35 196 88 273 288 72 160 416), lower := (rows 7 35 196 88 273 288 72 128 256), losses := [] }

theorem u387 : Upper (D 9) (R 9) [6,33,192,80,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b387 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 4, region := 106, targets := 128 },{ cop := 3, region := 132, targets := 32 }], pairs := [(1,7),(2,0),(2,5),(3,0),(3,7)], upper := (rows 7 35 196 88 273 288 96 136 392), lower := (rows 7 35 196 88 273 288 96 128 256), losses := [] }

theorem u388 : Upper (D 9) (R 9) [6,33,192,80,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b388 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 35 196 88 273 288 192 168 296), lower := (rows 7 35 196 88 273 288 192 128 256), losses := [] }

theorem u389 : Upper (D 9) (R 9) [6,33,192,80,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b389 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 88 304 40 65 384 384), lower := (rows 7 35 196 88 304 40 65 128 256), losses := [] }

theorem u390 : Upper (D 9) (R 9) [6,33,192,80,288,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b390 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 196 88 304 40 192 385 257), lower := (rows 7 35 196 88 304 40 192 128 256), losses := [] }

theorem u391 : Upper (D 9) (R 9) [6,33,192,80,288,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b391 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 35 196 88 304 40 320 129 385), lower := (rows 7 35 196 88 304 40 320 128 256), losses := [] }

theorem u392 : Upper (D 9) (R 9) [6,33,192,80,288,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b392 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 196 88 400 40 65 416 288), lower := (rows 7 35 196 88 400 40 65 128 256), losses := [] }

theorem u393 : Upper (D 9) (R 9) [6,33,192,80,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b393 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 196 88 400 40 96 385 257), lower := (rows 7 35 196 88 400 40 96 128 256), losses := [] }

theorem u394 : Upper (D 9) (R 9) [6,33,192,80,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b394 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 7 35 196 88 400 40 320 161 289), lower := (rows 7 35 196 88 400 40 320 128 256), losses := [] }

theorem u395 : Upper (D 9) (R 9) [6,33,192,80,384,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b395 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r396 : Route 9 := (fun mask => (mask,id))

def c396 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u396 : Upper (D 9) (R 9) [6,33,192,80,384,256,1] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,384,256,1] 13 (by decide) (choices 1) [8,32] r396 c396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u15
  · exact u16

def b397 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 76, targets := 288 }], pairs := [(2,5),(2,8),(3,5),(3,8)], upper := (rows 7 35 196 88 400 288 72 161 289), lower := (rows 7 35 196 88 400 288 72 128 256), losses := [] }

theorem u397 : Upper (D 9) (R 9) [6,33,192,80,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b397 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r398 : Route 9 := (fun mask => (mask,id))

def c398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u398 : Upper (D 9) (R 9) [6,33,192,80,384,256,32] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,384,256,32] 13 (by decide) (choices 1) [1,8] r398 c398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u17
  · exact u18

def b399 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 72, targets := 385 },{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(3,0),(3,7),(3,8)], upper := (rows 7 35 196 104 273 288 72 144 400), lower := (rows 7 35 196 104 273 288 72 128 256), losses := [] }

theorem u399 : Upper (D 9) (R 9) [6,33,192,96,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b399 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 4, region := 236, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 7 35 196 104 273 288 80 136 392), lower := (rows 7 35 196 104 273 288 80 128 256), losses := [] }

theorem u400 : Upper (D 9) (R 9) [6,33,192,96,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b400 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 35 196 104 273 288 192 152 280), lower := (rows 7 35 196 104 273 288 192 128 256), losses := [] }

theorem u401 : Upper (D 9) (R 9) [6,33,192,96,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b401 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5),(2,0),(3,0),(4,0)], upper := (rows 7 35 196 104 280 48 65 384 384), lower := (rows 7 35 196 104 280 48 65 128 256), losses := [] }

theorem u402 : Upper (D 9) (R 9) [6,33,192,96,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b402 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 196 104 280 48 192 385 257), lower := (rows 7 35 196 104 280 48 192 128 256), losses := [] }

theorem u403 : Upper (D 9) (R 9) [6,33,192,96,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b403 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b404 : PairBound 9 := { available := 129, camps := [{ cop := 6, region := 56, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 35 196 104 280 48 320 129 385), lower := (rows 7 35 196 104 280 48 320 128 256), losses := [] }

theorem u404 : Upper (D 9) (R 9) [6,33,192,96,264,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b404 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b405 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 1, region := 72, targets := 384 }], pairs := [(2,0),(3,0),(3,7),(3,8),(4,0)], upper := (rows 7 35 196 104 280 288 65 144 400), lower := (rows 7 35 196 104 280 288 65 128 256), losses := [] }

theorem u405 : Upper (D 9) (R 9) [6,33,192,96,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b405 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 88, targets := 129 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 7 35 196 104 280 288 80 129 385), lower := (rows 7 35 196 104 280 288 80 128 256), losses := [] }

theorem u406 : Upper (D 9) (R 9) [6,33,192,96,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b406 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 315, targets := 128 },{ cop := 6, region := 4, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7),(4,7)], upper := (rows 7 35 196 104 280 288 192 145 273), lower := (rows 7 35 196 104 280 288 192 128 256), losses := [] }

theorem u407 : Upper (D 9) (R 9) [6,33,192,96,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b407 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 264, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 7 35 196 104 400 48 65 392 264), lower := (rows 7 35 196 104 400 48 65 128 256), losses := [] }

theorem u408 : Upper (D 9) (R 9) [6,33,192,96,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b408 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b409 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 7 35 196 104 400 48 72 385 257), lower := (rows 7 35 196 104 400 48 72 128 256), losses := [] }

theorem u409 : Upper (D 9) (R 9) [6,33,192,96,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b409 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b410 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8)], upper := (rows 7 35 196 104 400 48 320 137 265), lower := (rows 7 35 196 104 400 48 320 128 256), losses := [] }

theorem u410 : Upper (D 9) (R 9) [6,33,192,96,384,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b410 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b411 : PairBound 9 := { available := 24, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 1, region := 72, targets := 384 }], pairs := [(2,0),(3,0),(3,7),(3,8),(4,0)], upper := (rows 7 35 196 104 400 288 65 152 280), lower := (rows 7 35 196 104 400 288 65 128 256), losses := [] }

theorem u411 : Upper (D 9) (R 9) [6,33,192,96,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b411 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b412 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 72, targets := 385 },{ cop := 2, region := 307, targets := 64 }], pairs := [(0,6),(3,0),(3,7),(3,8)], upper := (rows 7 35 196 104 400 288 72 145 273), lower := (rows 7 35 196 104 400 288 72 128 256), losses := [] }

theorem u412 : Upper (D 9) (R 9) [6,33,192,96,384,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b412 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b413 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 3, region := 135, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(3,7)], upper := (rows 7 35 196 104 400 288 80 137 265), lower := (rows 7 35 196 104 400 288 80 128 256), losses := [] }

theorem u413 : Upper (D 9) (R 9) [6,33,192,96,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b413 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b414 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 7 35 196 265 336 48 72 160 416), lower := (rows 7 35 196 265 336 48 72 128 256), losses := [] }

theorem u414 : Upper (D 9) (R 9) [6,33,192,257,320,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b414 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b415 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 392, targets := 96 },{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0),(3,5),(3,6),(4,0)], upper := (rows 7 35 196 265 336 48 96 136 392), lower := (rows 7 35 196 265 336 48 96 128 256), losses := [] }

theorem u415 : Upper (D 9) (R 9) [6,33,192,257,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b415 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 35 196 265 336 48 192 168 296), lower := (rows 7 35 196 265 336 48 192 128 256), losses := [] }

theorem u416 : Upper (D 9) (R 9) [6,33,192,257,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b416 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 444, targets := 1 },{ cop := 1, region := 400, targets := 64 }], pairs := [(2,0),(3,0),(4,0),(4,6)], upper := (rows 7 35 196 328 400 40 65 176 304), lower := (rows 7 35 196 328 400 40 65 128 256), losses := [] }

theorem u417 : Upper (D 9) (R 9) [6,33,192,320,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b417 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b418 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 35 196 328 400 40 80 161 289), lower := (rows 7 35 196 328 400 40 80 128 256), losses := [] }

theorem u418 : Upper (D 9) (R 9) [6,33,192,320,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b418 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b419 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 400, targets := 96 },{ cop := 4, region := 108, targets := 1 }], pairs := [(2,0),(3,0),(4,5),(4,6)], upper := (rows 7 35 196 328 400 40 96 145 273), lower := (rows 7 35 196 328 400 40 96 128 256), losses := [] }

theorem u419 : Upper (D 9) (R 9) [6,33,192,320,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b419 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P09

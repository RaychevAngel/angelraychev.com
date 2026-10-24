import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b360 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 306, targets := 192 }], pairs := [(1,6),(1,7),(4,6),(4,7)], upper := (rows 13 290 70 168 19 33 192 192 272), lower := (rows 13 290 70 168 19 33 192 192 256), losses := [] }

theorem u360 : Upper (D 7) (R 7) [12,288,66,160,3,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 185, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 13 290 70 168 19 48 192 129 320), lower := (rows 13 290 70 168 19 48 192 129 256), losses := [] }

theorem u361 : Upper (D 7) (R 7) [12,288,66,160,3,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b361 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 306, targets := 192 }], pairs := [(1,6),(1,7),(4,6)], upper := (rows 13 290 70 168 19 48 192 192 257), lower := (rows 13 290 70 168 19 48 192 192 256), losses := [] }

theorem u362 : Upper (D 7) (R 7) [12,288,66,160,3,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b362 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 128, camps := [{ cop := 3, region := 258, targets := 65 },{ cop := 4, region := 232, targets := 2 }], pairs := [(1,0),(1,6),(3,1)], upper := (rows 13 290 70 168 19 96 65 144 384), lower := (rows 13 290 70 168 19 96 65 144 256), losses := [] }

theorem u363 : Upper (D 7) (R 7) [12,288,66,160,3,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b363 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 274, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 13 290 70 168 146 96 65 129 272), lower := (rows 13 290 70 168 146 96 65 129 256), losses := [] }

theorem u364 : Upper (D 7) (R 7) [12,288,66,160,130,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 152, targets := 65 }], pairs := [(3,0),(3,6),(4,0)], upper := (rows 13 290 70 168 146 96 65 144 257), lower := (rows 13 290 70 168 146 96 65 144 256), losses := [] }

theorem u365 : Upper (D 7) (R 7) [12,288,66,160,130,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b365 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 157, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 290 84 168 145 96 66 129 258), lower := (rows 13 290 84 168 145 96 66 129 256), losses := [] }

theorem u366 : Upper (D 7) (R 7) [12,288,80,160,129,64,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b366 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 358, targets := 128 },{ cop := 8, region := 234, targets := 1 }], pairs := [(1,0),(1,7),(2,7),(3,0)], upper := (rows 13 290 84 168 145 96 66 130 257), lower := (rows 13 290 84 168 145 96 66 130 256), losses := [] }

theorem u367 : Upper (D 7) (R 7) [12,288,80,160,129,64,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 67 13 56 146 288 192 132 320), lower := (rows 35 67 13 56 146 288 192 132 256), losses := [] }

theorem u368 : Upper (D 7) (R 7) [34,65,9,48,130,256,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b368 [(5,8),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 56 146 288 192 192 260), lower := (rows 35 67 13 56 146 288 192 192 256), losses := [] }

theorem u369 : Upper (D 7) (R 7) [34,65,9,48,130,256,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b369 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 67 13 88 146 160 320 132 288), lower := (rows 35 67 13 88 146 160 320 132 256), losses := [] }

theorem u370 : Upper (D 7) (R 7) [34,65,9,80,130,128,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b370 [(6,8),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 184, targets := 1 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 67 13 88 146 160 320 160 260), lower := (rows 35 67 13 88 146 160 320 160 256), losses := [] }

theorem u371 : Upper (D 7) (R 7) [34,65,9,80,130,128,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b371 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 339, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 13 200 274 160 80 132 288), lower := (rows 35 67 13 200 274 160 80 132 256), losses := [] }

theorem u372 : Upper (D 7) (R 7) [34,65,9,192,258,128,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b372 [(6,4),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b373 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 338, targets := 160 }], pairs := [(1,5),(1,7),(4,5)], upper := (rows 35 67 13 200 274 160 80 160 260), lower := (rows 35 67 13 200 274 160 80 160 256), losses := [] }

theorem u373 : Upper (D 7) (R 7) [34,65,9,192,258,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b373 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b374 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 328, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 67 13 280 146 36 192 160 320), lower := (rows 35 67 13 280 146 36 192 160 256), losses := [] }

theorem u374 : Upper (D 7) (R 7) [34,65,9,272,130,4,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b374 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 13 280 146 36 192 192 288), lower := (rows 35 67 13 280 146 36 192 192 256), losses := [] }

theorem u375 : Upper (D 7) (R 7) [34,65,9,272,130,4,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b375 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b376 : PairBound 9 := { available := 4, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 67 28 104 145 160 320 130 260), lower := (rows 35 67 28 104 145 160 320 130 256), losses := [] }

theorem u376 : Upper (D 7) (R 7) [34,65,24,96,129,128,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b376 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b377 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 188, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 28 104 145 160 320 132 258), lower := (rows 35 67 28 104 145 160 320 132 256), losses := [] }

theorem u377 : Upper (D 7) (R 7) [34,65,24,96,129,128,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b377 [(6,8),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 307, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 67 44 138 273 48 192 132 320), lower := (rows 35 67 44 138 273 48 192 132 256), losses := [] }

theorem u378 : Upper (D 7) (R 7) [34,65,40,130,257,16,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b378 [(5,4),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 309, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 35 67 44 138 273 48 192 192 260), lower := (rows 35 67 44 138 273 48 192 192 256), losses := [] }

theorem u379 : Upper (D 7) (R 7) [34,65,40,130,257,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b379 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 5, region := 336, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 70 13 26 336 160 192 129 288), lower := (rows 35 70 13 26 336 160 192 129 256), losses := [] }

theorem u380 : Upper (D 7) (R 7) [34,68,9,18,320,128,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b380 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 165, targets := 64 },{ cop := 8, region := 240, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 70 13 26 336 160 192 160 257), lower := (rows 35 70 13 26 336 160 192 160 256), losses := [] }

theorem u381 : Upper (D 7) (R 7) [34,68,9,18,320,128,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b382 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 272, targets := 161 },{ cop := 4, region := 161, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 35 70 13 152 274 160 96 129 320), lower := (rows 35 70 13 152 274 160 96 129 256), losses := [] }

theorem u382 : Upper (D 7) (R 7) [34,68,9,144,258,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b383 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 96 },{ cop := 4, region := 232, targets := 3 }], pairs := [(3,0),(3,1),(4,5),(4,6)], upper := (rows 35 70 13 152 274 160 96 192 257), lower := (rows 35 70 13 152 274 160 96 192 256), losses := [] }

theorem u383 : Upper (D 7) (R 7) [34,68,9,144,258,128,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b383 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 70 13 266 145 160 80 160 320), lower := (rows 35 70 13 266 145 160 80 160 256), losses := [] }

theorem u384 : Upper (D 7) (R 7) [34,68,9,258,129,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b384 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 268, targets := 192 }], pairs := [(2,6),(2,7),(3,6)], upper := (rows 35 70 13 266 145 160 80 192 288), lower := (rows 35 70 13 266 145 160 80 192 256), losses := [] }

theorem u385 : Upper (D 7) (R 7) [34,68,9,258,129,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b385 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5),(2,5),(3,1),(4,1)], upper := (rows 35 70 14 25 336 160 192 129 288), lower := (rows 35 70 14 25 336 160 192 129 256), losses := [] }

theorem u386 : Upper (D 7) (R 7) [34,68,10,17,320,128,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b386 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 3, region := 230, targets := 1 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 35 70 14 25 336 160 192 160 257), lower := (rows 35 70 14 25 336 160 192 160 256), losses := [] }

theorem u387 : Upper (D 7) (R 7) [34,68,10,17,320,128,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 70 14 265 145 160 80 160 320), lower := (rows 35 70 14 265 145 160 80 160 256), losses := [] }

theorem u388 : Upper (D 7) (R 7) [34,68,10,257,129,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b388 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 268, targets := 192 }], pairs := [(2,6),(2,7),(3,6)], upper := (rows 35 70 14 265 145 160 80 192 288), lower := (rows 35 70 14 265 145 160 80 192 256), losses := [] }

theorem u389 : Upper (D 7) (R 7) [34,68,10,257,129,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b389 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 70 14 392 145 48 65 160 320), lower := (rows 35 70 14 392 145 48 65 160 256), losses := [] }

theorem u390 : Upper (D 7) (R 7) [34,68,10,384,129,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b390 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 4, region := 296, targets := 1 }], pairs := [(3,0),(3,1),(4,1)], upper := (rows 35 70 14 392 145 48 65 192 288), lower := (rows 35 70 14 392 145 48 65 192 256), losses := [] }

theorem u391 : Upper (D 7) (R 7) [34,68,10,384,129,16,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b391 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 366, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 35 70 14 392 145 48 96 129 320), lower := (rows 35 70 14 392 145 48 96 129 256), losses := [] }

theorem u392 : Upper (D 7) (R 7) [34,68,10,384,129,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b392 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 4, region := 264, targets := 32 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 35 70 14 392 145 48 96 192 257), lower := (rows 35 70 14 392 145 48 96 192 256), losses := [] }

theorem u393 : Upper (D 7) (R 7) [34,68,10,384,129,16,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b393 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 70 133 26 176 288 72 129 320), lower := (rows 35 70 133 26 176 288 72 129 256), losses := [] }

theorem u394 : Upper (D 7) (R 7) [34,68,129,18,160,256,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b394 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 216, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 35 70 133 26 176 288 72 192 257), lower := (rows 35 70 133 26 176 288 72 192 256), losses := [] }

theorem u395 : Upper (D 7) (R 7) [34,68,129,18,160,256,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b395 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 132, targets := 1 }], pairs := [(2,0),(3,1),(4,1)], upper := (rows 35 70 134 25 400 40 65 160 320), lower := (rows 35 70 134 25 400 40 65 160 256), losses := [] }

theorem u396 : Upper (D 7) (R 7) [34,68,130,17,384,8,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b396 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 32, camps := [{ cop := 6, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 25 400 40 65 192 288), lower := (rows 35 70 134 25 400 40 65 192 256), losses := [] }

theorem u397 : Upper (D 7) (R 7) [34,68,130,17,384,8,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b397 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 472, targets := 2 },{ cop := 0, region := 132, targets := 32 }], pairs := [(2,5),(3,1),(4,1)], upper := (rows 35 70 134 25 400 40 96 129 320), lower := (rows 35 70 134 25 400 40 96 129 256), losses := [] }

theorem u398 : Upper (D 7) (R 7) [34,68,130,17,384,8,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b398 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b399 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 25 400 40 96 192 257), lower := (rows 35 70 134 25 400 40 96 192 256), losses := [] }

theorem u399 : Upper (D 7) (R 7) [34,68,130,17,384,8,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b399 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5),(3,1),(4,1)], upper := (rows 35 70 134 88 176 288 65 129 264), lower := (rows 35 70 134 88 176 288 65 129 256), losses := [] }

theorem u400 : Upper (D 7) (R 7) [34,68,130,80,160,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b400 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 134, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 88 176 288 65 136 257), lower := (rows 35 70 134 88 176 288 65 136 256), losses := [] }

theorem u401 : Upper (D 7) (R 7) [34,68,130,80,160,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b401 [(5,8),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 35 70 134 168 273 48 65 136 320), lower := (rows 35 70 134 168 273 48 65 136 256), losses := [] }

theorem u402 : Upper (D 7) (R 7) [34,68,130,160,257,16,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b402 [(5,4),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 8, camps := [{ cop := 6, region := 134, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 134 168 273 48 65 192 264), lower := (rows 35 70 134 168 273 48 65 192 256), losses := [] }

theorem u403 : Upper (D 7) (R 7) [34,68,130,160,257,16,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b403 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b404 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 270, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 70 140 280 208 33 96 129 258), lower := (rows 35 70 140 280 208 33 96 129 256), losses := [] }

theorem u404 : Upper (D 7) (R 7) [34,68,136,272,192,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b404 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b405 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 144, targets := 33 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7),(4,0),(4,5)], upper := (rows 35 70 140 280 208 33 96 130 257), lower := (rows 35 70 140 280 208 33 96 130 256), losses := [] }

theorem u405 : Upper (D 7) (R 7) [34,68,136,272,192,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b405 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 262 25 208 160 65 136 288), lower := (rows 35 70 262 25 208 160 65 136 256), losses := [] }

theorem u406 : Upper (D 7) (R 7) [34,68,258,17,192,128,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b406 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 326, targets := 160 }], pairs := [(1,5),(1,7),(2,5),(2,7)], upper := (rows 35 70 262 25 208 160 65 160 264), lower := (rows 35 70 262 25 208 160 65 160 256), losses := [] }

theorem u407 : Upper (D 7) (R 7) [34,68,258,17,192,128,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b407 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 72, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(3,7),(4,1)], upper := (rows 35 70 262 104 152 160 65 129 272), lower := (rows 35 70 262 104 152 160 65 129 256), losses := [] }

theorem u408 : Upper (D 7) (R 7) [34,68,258,96,136,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b408 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b409 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 262 104 152 160 65 144 257), lower := (rows 35 70 262 104 152 160 65 144 256), losses := [] }

theorem u409 : Upper (D 7) (R 7) [34,68,258,96,136,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b409 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b410 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 302, targets := 1 },{ cop := 0, region := 216, targets := 32 }], pairs := [(1,0),(2,0),(3,0),(3,5)], upper := (rows 35 70 268 26 208 160 65 129 288), lower := (rows 35 70 268 26 208 160 65 129 256), losses := [] }

theorem u410 : Upper (D 7) (R 7) [34,68,264,18,192,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b410 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b411 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 184, targets := 1 },{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,0),(4,0)], upper := (rows 35 70 268 26 208 160 65 160 257), lower := (rows 35 70 268 26 208 160 65 160 256), losses := [] }

theorem u411 : Upper (D 7) (R 7) [34,68,264,18,192,128,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b411 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b412 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 169, targets := 64 },{ cop := 0, region := 80, targets := 2 },{ cop := 0, region := 136, targets := 32 }], pairs := [(0,6),(3,5),(3,6),(4,1)], upper := (rows 35 70 268 138 112 160 65 129 272), lower := (rows 35 70 268 138 112 160 65 129 256), losses := [] }

theorem u412 : Upper (D 7) (R 7) [34,68,264,130,96,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b412 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b413 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 184, targets := 1 },{ cop := 3, region := 33, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 70 268 138 112 160 65 144 257), lower := (rows 35 70 268 138 112 160 65 144 256), losses := [] }

theorem u413 : Upper (D 7) (R 7) [34,68,264,130,96,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b413 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b414 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 216, targets := 2 },{ cop := 0, region := 80, targets := 128 },{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6),(3,1),(4,1),(4,7)], upper := (rows 35 70 268 152 112 160 65 129 258), lower := (rows 35 70 268 152 112 160 65 129 256), losses := [] }

theorem u414 : Upper (D 7) (R 7) [34,68,264,144,96,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b414 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b415 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 80, targets := 130 },{ cop := 1, region := 184, targets := 1 }], pairs := [(3,0),(4,0),(4,1),(4,7)], upper := (rows 35 70 268 152 112 160 65 130 257), lower := (rows 35 70 268 152 112 160 65 130 256), losses := [] }

theorem u415 : Upper (D 7) (R 7) [34,68,264,144,96,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b415 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 262, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 25 208 40 96 129 258), lower := (rows 35 70 388 25 208 40 96 129 256), losses := [] }

theorem u416 : Upper (D 7) (R 7) [34,68,384,17,192,8,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b416 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 388, targets := 96 },{ cop := 1, region := 144, targets := 1 }], pairs := [(2,5),(2,6),(4,0)], upper := (rows 35 70 388 25 208 40 96 130 257), lower := (rows 35 70 388 25 208 40 96 130 256), losses := [] }

theorem u417 : Upper (D 7) (R 7) [34,68,384,17,192,8,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b417 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b418 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 70 388 26 176 33 72 129 320), lower := (rows 35 70 388 26 176 33 72 129 256), losses := [] }

theorem u418 : Upper (D 7) (R 7) [34,68,384,18,160,1,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b418 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b419 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 216, targets := 1 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(3,0),(4,0)], upper := (rows 35 70 388 26 176 33 72 192 257), lower := (rows 35 70 388 26 176 33 72 192 256), losses := [] }

theorem u419 : Upper (D 7) (R 7) [34,68,384,18,160,1,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b419 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P07

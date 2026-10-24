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

def b10380 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 291, targets := 128 },{ cop := 4, region := 362, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 37 322 196 56 145 34 72 131 259), lower := (rows 37 322 196 56 145 34 72 128 256), losses := [] }

theorem u10380 : Upper (D 7) (R 7) [36,320,192,48,129,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10380 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10381 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 109, targets := 2 },{ cop := 2, region := 33, targets := 128 }], pairs := [(0,1),(0,7),(2,1),(3,1)], upper := (rows 37 322 196 56 146 33 65 138 266), lower := (rows 37 322 196 56 146 33 65 128 256), losses := [] }

theorem u10381 : Upper (D 7) (R 7) [36,320,192,48,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10382 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 33, targets := 194 },{ cop := 8, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(0,7),(1,0)], upper := (rows 37 322 196 56 146 33 66 137 265), lower := (rows 37 322 196 56 146 33 66 128 256), losses := [] }

theorem u10382 : Upper (D 7) (R 7) [36,320,192,48,130,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10382 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10383 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 109, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 37 322 196 56 146 33 72 131 259), lower := (rows 37 322 196 56 146 33 72 128 256), losses := [] }

theorem u10383 : Upper (D 7) (R 7) [36,320,192,48,130,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10383 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10384 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 162 7 25 274 36 72 192 448), lower := (rows 97 162 7 25 274 36 72 128 256), losses := [] }

theorem u10384 : Upper (D 7) (R 7) [96,160,3,17,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10384 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10385 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(3,5),(4,5)], upper := (rows 97 162 7 25 274 36 192 200 328), lower := (rows 97 162 7 25 274 36 192 128 256), losses := [] }

theorem u10385 : Upper (D 7) (R 7) [96,160,3,17,258,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10385 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10386 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 162 7 25 400 36 66 200 328), lower := (rows 97 162 7 25 400 36 66 128 256), losses := [] }

theorem u10386 : Upper (D 7) (R 7) [96,160,3,17,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10386 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10387 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 402, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 97 162 7 25 400 36 72 194 322), lower := (rows 97 162 7 25 400 36 72 128 256), losses := [] }

theorem u10387 : Upper (D 7) (R 7) [96,160,3,17,384,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10387 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10388 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 81, targets := 2 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,1),(0,7),(4,1)], upper := (rows 97 162 7 28 208 288 65 138 266), lower := (rows 97 162 7 28 208 288 65 128 256), losses := [] }

theorem u10388 : Upper (D 7) (R 7) [96,160,3,20,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10388 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10389 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 80, targets := 33 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(4,0),(4,5)], upper := (rows 97 162 7 28 208 288 66 137 265), lower := (rows 97 162 7 28 208 288 66 128 256), losses := [] }

theorem u10389 : Upper (D 7) (R 7) [96,160,3,20,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10389 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10390 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 7 28 208 288 72 131 259), lower := (rows 97 162 7 28 208 288 72 128 256), losses := [] }

theorem u10390 : Upper (D 7) (R 7) [96,160,3,20,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10390 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10391 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 162 7 74 145 288 68 152 280), lower := (rows 97 162 7 74 145 288 68 128 256), losses := [] }

theorem u10391 : Upper (D 7) (R 7) [96,160,3,66,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10391 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10392 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 150, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 7 74 145 288 72 148 276), lower := (rows 97 162 7 74 145 288 72 128 256), losses := [] }

theorem u10392 : Upper (D 7) (R 7) [96,160,3,66,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10392 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10393 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 81, targets := 2 }], pairs := [(0,1),(4,1)], upper := (rows 97 162 7 74 145 288 80 140 268), lower := (rows 97 162 7 74 145 288 80 128 256), losses := [] }

theorem u10393 : Upper (D 7) (R 7) [96,160,3,66,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10393 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10394 : PairBound 9 := { available := 24, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 74 148 288 65 152 280), lower := (rows 97 162 7 74 148 288 65 128 256), losses := [] }

theorem u10394 : Upper (D 7) (R 7) [96,160,3,66,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10394 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10395 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 150, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 7 74 148 288 72 145 273), lower := (rows 97 162 7 74 148 288 72 128 256), losses := [] }

theorem u10395 : Upper (D 7) (R 7) [96,160,3,66,132,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10395 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10396 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 97 162 7 74 148 288 80 137 265), lower := (rows 97 162 7 74 148 288 80 128 256), losses := [] }

theorem u10396 : Upper (D 7) (R 7) [96,160,3,66,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10396 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10397 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 74 152 288 65 148 276), lower := (rows 97 162 7 74 152 288 65 128 256), losses := [] }

theorem u10397 : Upper (D 7) (R 7) [96,160,3,66,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10397 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10398 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 162 7 74 152 288 68 145 273), lower := (rows 97 162 7 74 152 288 68 128 256), losses := [] }

theorem u10398 : Upper (D 7) (R 7) [96,160,3,66,136,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10398 [(5,8),(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10399 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 88, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 97 162 7 74 152 288 80 133 261), lower := (rows 97 162 7 74 152 288 80 128 256), losses := [] }

theorem u10399 : Upper (D 7) (R 7) [96,160,3,66,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10399 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10400 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 74 276 48 65 136 392), lower := (rows 97 162 7 74 276 48 65 128 256), losses := [] }

theorem u10400 : Upper (D 7) (R 7) [96,160,3,66,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10400 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10401 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 7 74 276 48 72 129 385), lower := (rows 97 162 7 74 276 48 72 128 256), losses := [] }

theorem u10401 : Upper (D 7) (R 7) [96,160,3,66,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10401 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10402 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 97 162 7 74 276 48 192 137 265), lower := (rows 97 162 7 74 276 48 192 128 256), losses := [] }

theorem u10402 : Upper (D 7) (R 7) [96,160,3,66,260,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10402 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10403 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 97 162 7 76 152 288 65 146 274), lower := (rows 97 162 7 76 152 288 65 128 256), losses := [] }

theorem u10403 : Upper (D 7) (R 7) [96,160,3,68,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10403 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10404 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 7 76 152 288 66 145 273), lower := (rows 97 162 7 76 152 288 66 128 256), losses := [] }

theorem u10404 : Upper (D 7) (R 7) [96,160,3,68,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10404 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10405 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 7 76 152 288 80 131 259), lower := (rows 97 162 7 76 152 288 80 128 256), losses := [] }

theorem u10405 : Upper (D 7) (R 7) [96,160,3,68,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10405 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10406 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 162 7 88 273 36 66 136 392), lower := (rows 97 162 7 88 273 36 66 128 256), losses := [] }

theorem u10406 : Upper (D 7) (R 7) [96,160,3,80,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10406 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10407 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 97 162 7 88 273 36 72 130 386), lower := (rows 97 162 7 88 273 36 72 128 256), losses := [] }

theorem u10407 : Upper (D 7) (R 7) [96,160,3,80,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10407 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10408 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(3,5),(4,5)], upper := (rows 97 162 7 88 273 36 192 138 266), lower := (rows 97 162 7 88 273 36 192 128 256), losses := [] }

theorem u10408 : Upper (D 7) (R 7) [96,160,3,80,257,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10408 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10409 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 162 7 88 274 36 65 136 392), lower := (rows 97 162 7 88 274 36 65 128 256), losses := [] }

theorem u10409 : Upper (D 7) (R 7) [96,160,3,80,258,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10409 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10410 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 7 88 274 36 72 129 385), lower := (rows 97 162 7 88 274 36 72 128 256), losses := [] }

theorem u10410 : Upper (D 7) (R 7) [96,160,3,80,258,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10410 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10411 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 472, targets := 32 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(3,5),(4,5)], upper := (rows 97 162 7 88 274 36 192 137 265), lower := (rows 97 162 7 88 274 36 192 128 256), losses := [] }

theorem u10411 : Upper (D 7) (R 7) [96,160,3,80,258,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10411 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10412 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 162 7 88 400 36 65 138 266), lower := (rows 97 162 7 88 400 36 65 128 256), losses := [] }

theorem u10412 : Upper (D 7) (R 7) [96,160,3,80,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10412 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10413 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 162 7 88 400 36 66 137 265), lower := (rows 97 162 7 88 400 36 66 128 256), losses := [] }

theorem u10413 : Upper (D 7) (R 7) [96,160,3,80,384,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10413 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10414 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 97 162 7 88 400 36 72 131 259), lower := (rows 97 162 7 88 400 36 72 128 256), losses := [] }

theorem u10414 : Upper (D 7) (R 7) [96,160,3,80,384,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10414 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10415 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 162 7 200 273 36 66 152 280), lower := (rows 97 162 7 200 273 36 66 128 256), losses := [] }

theorem u10415 : Upper (D 7) (R 7) [96,160,3,192,257,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10415 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10416 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 406, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 7 200 273 36 72 146 274), lower := (rows 97 162 7 200 273 36 72 128 256), losses := [] }

theorem u10416 : Upper (D 7) (R 7) [96,160,3,192,257,4,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10416 [(5,2),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10417 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 138, targets := 1 }], pairs := [(1,0),(3,0)], upper := (rows 97 162 7 200 273 36 80 138 266), lower := (rows 97 162 7 200 273 36 80 128 256), losses := [] }

theorem u10417 : Upper (D 7) (R 7) [96,160,3,192,257,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10417 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10418 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 138, targets := 1 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(1,0),(3,0)], upper := (rows 97 162 7 200 276 48 65 138 266), lower := (rows 97 162 7 200 276 48 65 128 256), losses := [] }

theorem u10418 : Upper (D 7) (R 7) [96,160,3,192,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10418 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10419 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 34 },{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7),(3,1),(3,5)], upper := (rows 97 162 7 200 276 48 66 137 265), lower := (rows 97 162 7 200 276 48 66 128 256), losses := [] }

theorem u10419 : Upper (D 7) (R 7) [96,160,3,192,260,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10419 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10420 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 7 200 276 48 72 131 259), lower := (rows 97 162 7 200 276 48 72 128 256), losses := [] }

theorem u10420 : Upper (D 7) (R 7) [96,160,3,192,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10420 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10421 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 162 7 200 280 36 65 146 274), lower := (rows 97 162 7 200 280 36 65 128 256), losses := [] }

theorem u10421 : Upper (D 7) (R 7) [96,160,3,192,264,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10421 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10422 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 97 162 7 200 280 36 66 145 273), lower := (rows 97 162 7 200 280 36 66 128 256), losses := [] }

theorem u10422 : Upper (D 7) (R 7) [96,160,3,192,264,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10422 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10423 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 7 200 280 36 80 131 259), lower := (rows 97 162 7 200 280 36 80 128 256), losses := [] }

theorem u10423 : Upper (D 7) (R 7) [96,160,3,192,264,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10423 [(5,2),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10424 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 14 82 288 65 144 400), lower := (rows 97 162 13 14 82 288 65 128 256), losses := [] }

theorem u10424 : Upper (D 7) (R 7) [96,160,9,6,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10424 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10425 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 97 162 13 14 82 288 80 129 385), lower := (rows 97 162 13 14 82 288 80 128 256), losses := [] }

theorem u10425 : Upper (D 7) (R 7) [96,160,9,6,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10425 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10426 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 14 82 288 192 145 273), lower := (rows 97 162 13 14 82 288 192 128 256), losses := [] }

theorem u10426 : Upper (D 7) (R 7) [96,160,9,6,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10426 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10427 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 14 208 288 65 146 274), lower := (rows 97 162 13 14 208 288 65 128 256), losses := [] }

theorem u10427 : Upper (D 7) (R 7) [96,160,9,6,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10427 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10428 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 77, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 14 208 288 66 145 273), lower := (rows 97 162 13 14 208 288 66 128 256), losses := [] }

theorem u10428 : Upper (D 7) (R 7) [96,160,9,6,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10428 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10429 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 64 }], pairs := [(1,6),(2,6)], upper := (rows 97 162 13 14 208 288 80 131 259), lower := (rows 97 162 13 14 208 288 80 128 256), losses := [] }

theorem u10429 : Upper (D 7) (R 7) [96,160,9,6,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10429 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10430 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 26 84 288 65 130 386), lower := (rows 97 162 13 26 84 288 65 128 256), losses := [] }

theorem u10430 : Upper (D 7) (R 7) [96,160,9,18,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10430 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10431 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 93, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 97 162 13 26 84 288 66 129 385), lower := (rows 97 162 13 26 84 288 66 128 256), losses := [] }

theorem u10431 : Upper (D 7) (R 7) [96,160,9,18,68,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10431 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10432 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 64 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(1,6),(2,1)], upper := (rows 97 162 13 26 84 288 192 131 259), lower := (rows 97 162 13 26 84 288 192 128 256), losses := [{ target := 1, region := (rows 3 0 12 8 24 288 194 128 256), good := (rows 97 225 29 93 84 288 192 192 288) }] }

theorem u10432 : Upper (D 7) (R 7) [96,160,9,18,68,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10432 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10433 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 0, region := 130, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 97 162 13 26 148 288 65 194 322), lower := (rows 97 162 13 26 148 288 65 128 256), losses := [] }

theorem u10433 : Upper (D 7) (R 7) [96,160,9,18,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10433 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10434 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 357, targets := 128 },{ cop := 6, region := 289, targets := 2 }], pairs := [(0,1),(0,7),(2,7)], upper := (rows 97 162 13 26 148 288 66 193 321), lower := (rows 97 162 13 26 148 288 66 128 256), losses := [] }

theorem u10434 : Upper (D 7) (R 7) [96,160,9,18,132,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10434 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10435 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 101, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 97 162 13 26 336 36 65 130 386), lower := (rows 97 162 13 26 336 36 65 128 256), losses := [] }

theorem u10435 : Upper (D 7) (R 7) [96,160,9,18,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10435 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10436 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 34 },{ cop := 3, region := 101, targets := 128 }], pairs := [(0,7),(4,1),(4,5)], upper := (rows 97 162 13 26 336 36 66 129 385), lower := (rows 97 162 13 26 336 36 66 128 256), losses := [] }

theorem u10436 : Upper (D 7) (R 7) [96,160,9,18,320,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10436 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10437 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 130, targets := 64 },{ cop := 1, region := 65, targets := 2 }], pairs := [(0,1),(1,6),(2,1)], upper := (rows 97 162 13 26 336 36 192 131 259), lower := (rows 97 162 13 26 336 36 192 128 256), losses := [{ target := 1, region := (rows 11 0 12 8 16 44 194 128 256), good := (rows 97 225 45 125 336 36 192 192 256) }] }

theorem u10437 : Upper (D 7) (R 7) [96,160,9,18,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10437 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10438 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 101, targets := 128 },{ cop := 6, region := 33, targets := 2 }], pairs := [(0,1),(0,7),(2,7),(4,0)], upper := (rows 97 162 13 26 400 33 66 196 324), lower := (rows 97 162 13 26 400 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 32 74 132 260), good := (rows 96 226 476 90 400 32 66 128 256) }] }

theorem u10438 : Upper (D 7) (R 7) [96,160,9,18,384,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10438 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10439 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 410, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 97 162 13 26 400 33 68 194 322), lower := (rows 97 162 13 26 400 33 68 128 256), losses := [] }

theorem u10439 : Upper (D 7) (R 7) [96,160,9,18,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10439 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u10439
end Delivery.IrregularNine14.P07

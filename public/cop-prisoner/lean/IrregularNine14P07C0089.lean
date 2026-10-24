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

def b5340 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 164 25 208 288 65 138 266), lower := (rows 35 70 164 25 208 288 65 128 256), losses := [] }

theorem u5340 : Upper (D 7) (R 7) [34,68,160,17,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5340 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5341 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 70 164 25 208 288 66 137 265), lower := (rows 35 70 164 25 208 288 66 128 256), losses := [] }

theorem u5341 : Upper (D 7) (R 7) [34,68,160,17,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5341 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5342 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 70 164 25 208 288 72 131 259), lower := (rows 35 70 164 25 208 288 72 128 256), losses := [] }

theorem u5342 : Upper (D 7) (R 7) [34,68,160,17,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5342 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5343 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 70 164 73 145 288 66 152 280), lower := (rows 35 70 164 73 145 288 66 128 256), losses := [] }

theorem u5343 : Upper (D 7) (R 7) [34,68,160,65,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5343 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5344 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 164 73 145 288 72 146 274), lower := (rows 35 70 164 73 145 288 72 128 256), losses := [] }

theorem u5344 : Upper (D 7) (R 7) [34,68,160,65,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5344 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5345 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 35 70 164 73 145 288 80 138 266), lower := (rows 35 70 164 73 145 288 80 128 256), losses := [] }

theorem u5345 : Upper (D 7) (R 7) [34,68,160,65,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5345 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5346 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 35 70 164 73 152 288 65 146 274), lower := (rows 35 70 164 73 152 288 65 128 256), losses := [] }

theorem u5346 : Upper (D 7) (R 7) [34,68,160,65,136,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5346 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5347 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 70 164 73 152 288 66 145 273), lower := (rows 35 70 164 73 152 288 66 128 256), losses := [] }

theorem u5347 : Upper (D 7) (R 7) [34,68,160,65,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5347 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5348 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 70 164 73 152 288 80 131 259), lower := (rows 35 70 164 73 152 288 80 128 256), losses := [] }

theorem u5348 : Upper (D 7) (R 7) [34,68,160,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5348 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5349 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 436, targets := 66 }], pairs := [(2,1),(2,6),(4,1)], upper := (rows 35 70 164 73 273 48 66 136 392), lower := (rows 35 70 164 73 273 48 66 128 256), losses := [] }

theorem u5349 : Upper (D 7) (R 7) [34,68,160,65,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5349 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5350 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 164 73 273 48 72 130 386), lower := (rows 35 70 164 73 273 48 72 128 256), losses := [] }

theorem u5350 : Upper (D 7) (R 7) [34,68,160,65,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5350 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5351 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 313, targets := 128 }], pairs := [(0,7),(3,7),(4,7)], upper := (rows 35 70 164 73 273 48 192 138 266), lower := (rows 35 70 164 73 273 48 192 128 256), losses := [] }

theorem u5351 : Upper (D 7) (R 7) [34,68,160,65,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5351 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5352 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 35 70 164 88 145 288 65 138 266), lower := (rows 35 70 164 88 145 288 65 128 256), losses := [] }

theorem u5352 : Upper (D 7) (R 7) [34,68,160,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5352 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5353 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 35 70 164 88 145 288 66 137 265), lower := (rows 35 70 164 88 145 288 66 128 256), losses := [] }

theorem u5353 : Upper (D 7) (R 7) [34,68,160,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5353 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5354 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 70 164 88 145 288 72 131 259), lower := (rows 35 70 164 88 145 288 72 128 256), losses := [] }

theorem u5354 : Upper (D 7) (R 7) [34,68,160,80,129,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5354 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5355 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 66, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 35 70 164 137 273 48 66 200 328), lower := (rows 35 70 164 137 273 48 66 128 256), losses := [] }

theorem u5355 : Upper (D 7) (R 7) [34,68,160,129,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5355 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5356 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 35 70 164 137 273 48 72 194 322), lower := (rows 35 70 164 137 273 48 72 128 256), losses := [] }

theorem u5356 : Upper (D 7) (R 7) [34,68,160,129,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5356 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5357 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 164 200 273 48 65 138 266), lower := (rows 35 70 164 200 273 48 65 128 256), losses := [] }

theorem u5357 : Upper (D 7) (R 7) [34,68,160,192,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5357 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5358 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 70 164 200 273 48 66 137 265), lower := (rows 35 70 164 200 273 48 66 128 256), losses := [] }

theorem u5358 : Upper (D 7) (R 7) [34,68,160,192,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5358 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5359 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 74, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 164 200 273 48 72 131 259), lower := (rows 35 70 164 200 273 48 72 128 256), losses := [] }

theorem u5359 : Upper (D 7) (R 7) [34,68,160,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5359 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5360 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 88, targets := 128 }], pairs := [(1,0),(1,5),(1,7),(3,7)], upper := (rows 35 70 261 25 112 160 66 136 392), lower := (rows 35 70 261 25 112 160 66 128 256), losses := [] }

theorem u5360 : Upper (D 7) (R 7) [34,68,257,17,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5360 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5361 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 261 25 112 160 72 130 386), lower := (rows 35 70 261 25 112 160 72 128 256), losses := [] }

theorem u5361 : Upper (D 7) (R 7) [34,68,257,17,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5361 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5362 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 261 25 112 160 192 138 266), lower := (rows 35 70 261 25 112 160 192 128 256), losses := [] }

theorem u5362 : Upper (D 7) (R 7) [34,68,257,17,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5362 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5363 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 1, region := 176, targets := 1 }], pairs := [(0,6),(3,6),(4,0)], upper := (rows 35 70 261 25 146 160 72 224 352), lower := (rows 35 70 261 25 146 160 72 128 256), losses := [] }

theorem u5363 : Upper (D 7) (R 7) [34,68,257,17,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5363 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5364 : PairBound 9 := { available := 72, camps := [{ cop := 4, region := 41, targets := 64 },{ cop := 3, region := 484, targets := 2 }], pairs := [(0,6),(1,0),(2,1),(3,6)], upper := (rows 35 70 261 25 146 160 96 200 328), lower := (rows 35 70 261 25 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 184 249 136 264), good := (rows 98 70 326 504 242 224 96 224 256) }] }

theorem u5364 : Upper (D 7) (R 7) [34,68,257,17,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5364 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5365 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 3, region := 420, targets := 2 }], pairs := [(1,0),(1,5),(1,7),(2,1)], upper := (rows 35 70 261 25 208 160 66 168 296), lower := (rows 35 70 261 25 208 160 66 128 256), losses := [] }

theorem u5365 : Upper (D 7) (R 7) [34,68,257,17,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5365 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5366 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 260, targets := 128 }], pairs := [(0,6),(2,6),(2,7)], upper := (rows 35 70 261 25 208 160 72 162 290), lower := (rows 35 70 261 25 208 160 72 128 256), losses := [] }

theorem u5366 : Upper (D 7) (R 7) [34,68,257,17,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5366 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5367 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 80, targets := 3 }], pairs := [(1,0),(3,1),(4,0),(4,1)], upper := (rows 35 70 261 25 208 160 96 138 266), lower := (rows 35 70 261 25 208 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 176 176 249 128 256), good := (rows 114 70 326 120 240 240 112 240 256) },{ target := 1, region := (rows 1 0 4 9 176 176 249 128 256), good := (rows 121 68 333 121 240 240 112 240 256) }] }

theorem u5367 : Upper (D 7) (R 7) [34,68,257,17,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5367 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5368 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 90, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 35 70 261 26 81 160 72 160 416), lower := (rows 35 70 261 26 81 160 72 128 256), losses := [] }

theorem u5368 : Upper (D 7) (R 7) [34,68,257,18,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5368 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5369 : PairBound 9 := { available := 136, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 88, targets := 128 }], pairs := [(1,5),(2,5),(3,5),(3,7)], upper := (rows 35 70 261 26 81 160 96 136 392), lower := (rows 35 70 261 26 81 160 96 128 256), losses := [] }

theorem u5369 : Upper (D 7) (R 7) [34,68,257,18,65,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5369 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5370 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,1)], upper := (rows 35 70 261 26 81 160 192 168 296), lower := (rows 35 70 261 26 81 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 232 232 136 264), good := (rows 113 100 277 504 113 224 224 224 256) },{ target := 5, region := (rows 1 2 4 9 17 0 224 128 256), good := (rows 91 70 285 26 89 192 192 192 256) }] }

theorem u5370 : Upper (D 7) (R 7) [34,68,257,18,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5370 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5371 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 88, targets := 128 },{ cop := 1, region := 184, targets := 1 }], pairs := [(3,0),(3,7),(4,0),(4,7)], upper := (rows 35 70 261 26 112 160 65 136 392), lower := (rows 35 70 261 26 112 160 65 128 256), losses := [] }

theorem u5371 : Upper (D 7) (R 7) [34,68,257,18,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5371 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5372 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 88, targets := 1 },{ cop := 0, region := 388, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 35 70 261 26 112 160 72 129 385), lower := (rows 35 70 261 26 112 160 72 128 256), losses := [] }

theorem u5372 : Upper (D 7) (R 7) [34,68,257,18,96,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5372 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5373 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 35 70 261 26 112 160 192 137 265), lower := (rows 35 70 261 26 112 160 192 128 256), losses := [] }

theorem u5373 : Upper (D 7) (R 7) [34,68,257,18,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5373 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5374 : PairBound 9 := { available := 96, camps := [], pairs := [(0,6),(2,1),(4,1)], upper := (rows 35 70 261 26 145 160 72 224 352), lower := (rows 35 70 261 26 145 160 72 128 256), losses := [{ target := 1, region := (rows 1 0 5 8 17 251 72 202 330), good := (rows 437 484 309 504 181 160 488 160 256) },{ target := 6, region := (rows 9 2 4 8 16 176 0 128 256), good := (rows 35 6 261 59 177 160 9 160 256) }] }

theorem u5374 : Upper (D 7) (R 7) [34,68,257,18,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5374 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5375 : PairBound 9 := { available := 72, camps := [], pairs := [(0,6),(1,0),(1,7),(2,7)], upper := (rows 35 70 261 26 145 160 96 200 328), lower := (rows 35 70 261 26 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 8 16 184 249 136 264), good := (rows 98 70 326 506 240 224 96 224 256) },{ target := 6, region := (rows 9 2 4 8 16 176 0 128 256), good := (rows 35 6 261 59 177 160 32 160 256) },{ target := 7, region := (rows 1 22 20 24 16 32 97 0 272), good := (rows 99 70 327 286 351 96 96 0 256) }] }

theorem u5375 : Upper (D 7) (R 7) [34,68,257,18,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5375 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5376 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 184, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 261 26 208 160 65 168 296), lower := (rows 35 70 261 26 208 160 65 128 256), losses := [] }

theorem u5376 : Upper (D 7) (R 7) [34,68,257,18,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5376 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5377 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 260, targets := 66 },{ cop := 0, region := 260, targets := 128 }], pairs := [(2,1),(2,6),(2,7)], upper := (rows 35 70 261 26 208 160 72 161 289), lower := (rows 35 70 261 26 208 160 72 128 256), losses := [] }

theorem u5377 : Upper (D 7) (R 7) [34,68,257,18,192,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5377 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5378 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 421, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(2,6),(4,0),(4,1)], upper := (rows 35 70 261 26 208 160 96 137 265), lower := (rows 35 70 261 26 208 160 96 128 256), losses := [] }

theorem u5378 : Upper (D 7) (R 7) [34,68,257,18,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5378 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5379 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 82, targets := 160 }], pairs := [(1,5),(1,7),(4,5),(4,7)], upper := (rows 35 70 261 56 81 160 66 136 392), lower := (rows 35 70 261 56 81 160 66 128 256), losses := [] }

theorem u5379 : Upper (D 7) (R 7) [34,68,257,48,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5379 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5380 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 88, targets := 130 }], pairs := [(3,1),(3,7),(4,1)], upper := (rows 35 70 261 56 81 160 72 130 386), lower := (rows 35 70 261 56 81 160 72 128 256), losses := [] }

theorem u5380 : Upper (D 7) (R 7) [34,68,257,48,65,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5380 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5381 : PairBound 9 := { available := 10, camps := [], pairs := [(3,0),(3,1),(4,1),(4,5)], upper := (rows 35 70 261 56 81 160 192 138 266), lower := (rows 35 70 261 56 81 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 224 224 128 256), good := (rows 98 102 260 120 120 224 224 224 256) },{ target := 1, region := (rows 1 0 4 25 17 224 224 128 256), good := (rows 121 100 285 120 121 224 224 224 256) },{ target := 5, region := (rows 1 2 4 8 17 0 224 128 256), good := (rows 83 70 277 88 81 192 192 192 256) }] }

theorem u5381 : Upper (D 7) (R 7) [34,68,257,48,65,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5381 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5382 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 74, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 35 70 261 73 146 160 72 176 304), lower := (rows 35 70 261 73 146 160 72 128 256), losses := [] }

theorem u5382 : Upper (D 7) (R 7) [34,68,257,65,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5382 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5383 : PairBound 9 := { available := 40, camps := [{ cop := 3, region := 420, targets := 66 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(2,1),(2,6)], upper := (rows 35 70 261 73 146 160 80 168 296), lower := (rows 35 70 261 73 146 160 80 128 256), losses := [] }

theorem u5383 : Upper (D 7) (R 7) [34,68,257,65,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5383 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5384 : PairBound 9 := { available := 24, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 261 73 146 160 96 152 280), lower := (rows 35 70 261 73 146 160 96 128 256), losses := [] }

theorem u5384 : Upper (D 7) (R 7) [34,68,257,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5384 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5385 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 74, targets := 160 }], pairs := [(1,5),(1,7),(3,5),(3,7)], upper := (rows 35 70 261 73 152 160 66 176 304), lower := (rows 35 70 261 73 152 160 66 128 256), losses := [] }

theorem u5385 : Upper (D 7) (R 7) [34,68,257,65,136,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5385 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5386 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 421, targets := 64 },{ cop := 0, region := 260, targets := 128 }], pairs := [(0,6),(2,6),(2,7)], upper := (rows 35 70 261 73 152 160 80 162 290), lower := (rows 35 70 261 73 152 160 80 128 256), losses := [] }

theorem u5386 : Upper (D 7) (R 7) [34,68,257,65,136,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5386 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5387 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 2 }], pairs := [(1,5),(2,5),(3,1),(4,5)], upper := (rows 35 70 261 73 152 160 96 146 274), lower := (rows 35 70 261 73 152 160 96 128 256), losses := [] }

theorem u5387 : Upper (D 7) (R 7) [34,68,257,65,136,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5387 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5388 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 35 70 261 88 145 160 66 168 296), lower := (rows 35 70 261 88 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 184 71 152 280), good := (rows 98 70 326 504 504 160 66 160 256) }] }

theorem u5388 : Upper (D 7) (R 7) [34,68,257,80,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5388 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5389 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 261 88 145 160 72 162 290), lower := (rows 35 70 261 88 145 160 72 128 256), losses := [] }

theorem u5389 : Upper (D 7) (R 7) [34,68,257,80,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5389 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5390 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 104, targets := 3 }], pairs := [(1,0),(1,5),(3,0),(3,1)], upper := (rows 35 70 261 88 145 160 96 138 266), lower := (rows 35 70 261 88 145 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 176 249 128 256), good := (rows 98 70 326 120 248 224 96 224 256) },{ target := 5, region := (rows 1 10 21 10 21 0 64 139 267), good := (rows 415 478 405 478 405 128 64 128 256) }] }

theorem u5390 : Upper (D 7) (R 7) [34,68,257,80,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5390 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5391 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 184, targets := 1 },{ cop := 2, region := 66, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 70 261 88 146 160 65 168 296), lower := (rows 35 70 261 88 146 160 65 128 256), losses := [] }

theorem u5391 : Upper (D 7) (R 7) [34,68,257,80,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5391 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5392 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 261 88 146 160 72 161 289), lower := (rows 35 70 261 88 146 160 72 128 256), losses := [] }

theorem u5392 : Upper (D 7) (R 7) [34,68,257,80,130,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5392 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5393 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 104, targets := 3 },{ cop := 4, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(3,1)], upper := (rows 35 70 261 88 146 160 96 137 265), lower := (rows 35 70 261 88 146 160 96 128 256), losses := [{ target := 0, region := (rows 0 6 4 24 16 176 249 128 256), good := (rows 98 70 326 120 250 224 96 224 256) }] }

theorem u5393 : Upper (D 7) (R 7) [34,68,257,80,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5393 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5394 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 66, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 261 104 145 48 66 136 392), lower := (rows 35 70 261 104 145 48 66 128 256), losses := [] }

theorem u5394 : Upper (D 7) (R 7) [34,68,257,96,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5394 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5395 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 70 261 104 145 48 72 130 386), lower := (rows 35 70 261 104 145 48 72 128 256), losses := [] }

theorem u5395 : Upper (D 7) (R 7) [34,68,257,96,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5395 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5396 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 261 104 145 48 192 138 266), lower := (rows 35 70 261 104 145 48 192 128 256), losses := [] }

theorem u5396 : Upper (D 7) (R 7) [34,68,257,96,129,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5396 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5397 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 66, targets := 161 },{ cop := 0, region := 72, targets := 1 }], pairs := [(1,0),(1,5),(1,7),(3,0)], upper := (rows 35 70 261 104 145 160 66 152 280), lower := (rows 35 70 261 104 145 160 66 128 256), losses := [] }

theorem u5397 : Upper (D 7) (R 7) [34,68,257,96,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5397 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5398 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 70 261 104 145 160 72 146 274), lower := (rows 35 70 261 104 145 160 72 128 256), losses := [] }

theorem u5398 : Upper (D 7) (R 7) [34,68,257,96,129,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5398 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5399 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 263, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 70 261 104 145 160 80 138 266), lower := (rows 35 70 261 104 145 160 80 128 256), losses := [] }

theorem u5399 : Upper (D 7) (R 7) [34,68,257,96,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5399 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u5399
end Delivery.IrregularNine14.P07

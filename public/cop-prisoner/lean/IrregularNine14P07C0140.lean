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

def b8400 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7)], upper := (rows 37 194 7 73 152 48 66 416 288), lower := (rows 37 194 7 73 152 48 66 128 256), losses := [] }

theorem u8400 : Upper (D 7) (R 7) [36,192,3,65,136,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8400 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8401 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 7 73 152 48 96 386 258), lower := (rows 37 194 7 73 152 48 96 128 256), losses := [] }

theorem u8401 : Upper (D 7) (R 7) [36,192,3,65,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8401 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8402 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 178, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 37 194 7 73 152 48 320 162 290), lower := (rows 37 194 7 73 152 48 320 128 256), losses := [] }

theorem u8402 : Upper (D 7) (R 7) [36,192,3,65,136,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8402 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8403 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7)], upper := (rows 37 194 7 73 152 288 66 176 304), lower := (rows 37 194 7 73 152 288 66 128 256), losses := [] }

theorem u8403 : Upper (D 7) (R 7) [36,192,3,65,136,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8403 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8404 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 293, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 7 73 152 288 80 162 290), lower := (rows 37 194 7 73 152 288 80 128 256), losses := [] }

theorem u8404 : Upper (D 7) (R 7) [36,192,3,65,136,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8404 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8405 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 7 73 152 288 96 146 274), lower := (rows 37 194 7 73 152 288 96 128 256), losses := [] }

theorem u8405 : Upper (D 7) (R 7) [36,192,3,65,136,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8405 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8406 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7)], upper := (rows 37 194 7 73 176 288 66 152 280), lower := (rows 37 194 7 73 176 288 66 128 256), losses := [] }

theorem u8406 : Upper (D 7) (R 7) [36,192,3,65,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8406 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8407 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 37 194 7 73 176 288 72 146 274), lower := (rows 37 194 7 73 176 288 72 128 256), losses := [] }

theorem u8407 : Upper (D 7) (R 7) [36,192,3,65,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8407 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8408 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 37 194 7 73 176 288 80 138 266), lower := (rows 37 194 7 73 176 288 80 128 256), losses := [] }

theorem u8408 : Upper (D 7) (R 7) [36,192,3,65,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8408 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8409 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7)], upper := (rows 37 194 7 73 280 48 66 160 416), lower := (rows 37 194 7 73 280 48 66 128 256), losses := [] }

theorem u8409 : Upper (D 7) (R 7) [36,192,3,65,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8409 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8410 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 7 73 280 48 96 130 386), lower := (rows 37 194 7 73 280 48 96 128 256), losses := [] }

theorem u8410 : Upper (D 7) (R 7) [36,192,3,65,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8410 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8411 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 73 280 48 192 162 290), lower := (rows 37 194 7 73 280 48 192 128 256), losses := [] }

theorem u8411 : Upper (D 7) (R 7) [36,192,3,65,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8411 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8412 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 72, targets := 160 },{ cop := 3, region := 434, targets := 1 }], pairs := [(1,0),(3,5),(3,7)], upper := (rows 37 194 7 73 400 48 66 168 296), lower := (rows 37 194 7 73 400 48 66 128 256), losses := [] }

theorem u8412 : Upper (D 7) (R 7) [36,192,3,65,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8412 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8413 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 37 194 7 73 400 48 72 162 290), lower := (rows 37 194 7 73 400 48 72 128 256), losses := [] }

theorem u8413 : Upper (D 7) (R 7) [36,192,3,65,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8413 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8414 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5),(2,5),(4,5)], upper := (rows 37 194 7 73 400 48 96 138 266), lower := (rows 37 194 7 73 400 48 96 128 256), losses := [] }

theorem u8414 : Upper (D 7) (R 7) [36,192,3,65,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8414 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8415 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 194 7 88 176 288 65 138 266), lower := (rows 37 194 7 88 176 288 65 128 256), losses := [] }

theorem u8415 : Upper (D 7) (R 7) [36,192,3,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8415 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8416 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 7 88 176 288 66 137 265), lower := (rows 37 194 7 88 176 288 66 128 256), losses := [] }

theorem u8416 : Upper (D 7) (R 7) [36,192,3,80,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8416 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8417 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 37 194 7 88 176 288 72 131 259), lower := (rows 37 194 7 88 176 288 72 128 256), losses := [] }

theorem u8417 : Upper (D 7) (R 7) [36,192,3,80,160,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8417 [(5,8),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8418 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 37 194 7 88 273 40 66 160 416), lower := (rows 37 194 7 88 273 40 66 128 256), losses := [] }

theorem u8418 : Upper (D 7) (R 7) [36,192,3,80,257,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8418 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8419 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 400, targets := 96 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 37 194 7 88 273 40 96 130 386), lower := (rows 37 194 7 88 273 40 96 128 256), losses := [] }

theorem u8419 : Upper (D 7) (R 7) [36,192,3,80,257,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8419 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8420 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 88 273 40 192 162 290), lower := (rows 37 194 7 88 273 40 192 128 256), losses := [] }

theorem u8420 : Upper (D 7) (R 7) [36,192,3,80,257,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8420 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8421 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 88 274 40 65 160 416), lower := (rows 37 194 7 88 274 40 65 128 256), losses := [] }

theorem u8421 : Upper (D 7) (R 7) [36,192,3,80,258,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8421 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8422 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 109, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 88 274 40 96 129 385), lower := (rows 37 194 7 88 274 40 96 128 256), losses := [] }

theorem u8422 : Upper (D 7) (R 7) [36,192,3,80,258,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8422 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8423 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 88 274 40 192 161 289), lower := (rows 37 194 7 88 274 40 192 128 256), losses := [] }

theorem u8423 : Upper (D 7) (R 7) [36,192,3,80,258,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8423 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8424 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 37, targets := 64 }], pairs := [(0,6),(1,0),(3,0),(4,0)], upper := (rows 37 194 7 88 280 160 65 162 290), lower := (rows 37 194 7 88 280 160 65 128 256), losses := [] }

theorem u8424 : Upper (D 7) (R 7) [36,192,3,80,264,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8425 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 2, region := 161, targets := 2 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(1,0),(2,6)], upper := (rows 37 194 7 88 280 160 66 161 289), lower := (rows 37 194 7 88 280 160 66 128 256), losses := [] }

theorem u8425 : Upper (D 7) (R 7) [36,192,3,80,264,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8425 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8426 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 37, targets := 64 },{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(0,6),(1,0),(2,6)], upper := (rows 37 194 7 88 280 160 96 131 259), lower := (rows 37 194 7 88 280 160 96 128 256), losses := [{ target := 1, region := (rows 5 0 4 8 16 162 231 128 256), good := (rows 101 224 101 88 280 224 96 224 256) }] }

theorem u8426 : Upper (D 7) (R 7) [36,192,3,80,264,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8427 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 194 7 88 400 40 65 162 290), lower := (rows 37 194 7 88 400 40 65 128 256), losses := [] }

theorem u8427 : Upper (D 7) (R 7) [36,192,3,80,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8427 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8428 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(4,1),(4,6)], upper := (rows 37 194 7 88 400 40 66 161 289), lower := (rows 37 194 7 88 400 40 66 128 256), losses := [] }

theorem u8428 : Upper (D 7) (R 7) [36,192,3,80,384,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8428 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8429 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 400, targets := 96 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 37 194 7 88 400 40 96 131 259), lower := (rows 37 194 7 88 400 40 96 128 256), losses := [] }

theorem u8429 : Upper (D 7) (R 7) [36,192,3,80,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8429 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8430 : PairBound 9 := { available := 130, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 194 7 104 280 48 65 130 386), lower := (rows 37 194 7 104 280 48 65 128 256), losses := [] }

theorem u8430 : Upper (D 7) (R 7) [36,192,3,96,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8430 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8431 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 198, targets := 32 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 37 194 7 104 280 48 66 129 385), lower := (rows 37 194 7 104 280 48 66 128 256), losses := [] }

theorem u8431 : Upper (D 7) (R 7) [36,192,3,96,264,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8431 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8432 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 7 104 280 48 192 131 259), lower := (rows 37 194 7 104 280 48 192 128 256), losses := [] }

theorem u8432 : Upper (D 7) (R 7) [36,192,3,96,264,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8432 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8433 : PairBound 9 := { available := 10, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 37 194 7 104 400 48 65 138 266), lower := (rows 37 194 7 104 400 48 65 128 256), losses := [] }

theorem u8433 : Upper (D 7) (R 7) [36,192,3,96,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8433 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8434 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 4, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 7 104 400 48 66 137 265), lower := (rows 37 194 7 104 400 48 66 128 256), losses := [] }

theorem u8434 : Upper (D 7) (R 7) [36,192,3,96,384,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8434 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8435 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 309, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 37 194 7 104 400 48 72 131 259), lower := (rows 37 194 7 104 400 48 72 128 256), losses := [] }

theorem u8435 : Upper (D 7) (R 7) [36,192,3,96,384,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8435 [(5,4),(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8436 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 13 88 50 288 65 130 386), lower := (rows 37 194 13 88 50 288 65 128 256), losses := [] }

theorem u8436 : Upper (D 7) (R 7) [36,192,9,80,34,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8436 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8437 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 421, targets := 66 }], pairs := [(0,1),(0,6),(2,1)], upper := (rows 37 194 13 88 50 288 66 129 385), lower := (rows 37 194 13 88 50 288 66 128 256), losses := [] }

theorem u8437 : Upper (D 7) (R 7) [36,192,9,80,34,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8437 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8438 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 37 194 13 88 50 288 192 131 259), lower := (rows 37 194 13 88 50 288 192 128 256), losses := [] }

theorem u8438 : Upper (D 7) (R 7) [36,192,9,80,34,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8438 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8439 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 32 },{ cop := 0, region := 400, targets := 2 }], pairs := [(1,5),(2,5),(3,5),(4,1)], upper := (rows 37 194 13 88 145 34 66 416 288), lower := (rows 37 194 13 88 145 34 66 128 256), losses := [] }

theorem u8439 : Upper (D 7) (R 7) [36,192,9,80,129,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8439 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8440 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 3, region := 386, targets := 32 }], pairs := [(0,1),(1,0),(1,5),(3,0)], upper := (rows 37 194 13 88 145 34 96 386 258), lower := (rows 37 194 13 88 145 34 96 128 256), losses := [{ target := 1, region := (rows 97 0 127 58 18 32 97 128 256), good := (rows 109 221 77 93 221 125 109 128 256) }] }

theorem u8440 : Upper (D 7) (R 7) [36,192,9,80,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8440 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8441 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0),(3,0),(4,6)], upper := (rows 37 194 13 88 145 34 320 162 290), lower := (rows 37 194 13 88 145 34 320 128 256), losses := [{ target := 6, region := (rows 1 2 4 8 17 34 0 162 290), good := (rows 437 418 29 24 145 418 256 128 256) }] }

theorem u8441 : Upper (D 7) (R 7) [36,192,9,80,129,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8441 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8442 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 78, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 37 194 13 88 145 288 66 162 290), lower := (rows 37 194 13 88 145 288 66 128 256), losses := [] }

theorem u8442 : Upper (D 7) (R 7) [36,192,9,80,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8442 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8443 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 362, targets := 1 },{ cop := 3, region := 130, targets := 32 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 13 88 145 288 96 130 258), lower := (rows 37 194 13 88 145 288 96 128 256), losses := [] }

theorem u8443 : Upper (D 7) (R 7) [36,192,9,80,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8443 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8444 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1)], upper := (rows 37 194 13 88 176 288 65 130 258), lower := (rows 37 194 13 88 176 288 65 128 256), losses := [] }

theorem u8444 : Upper (D 7) (R 7) [36,192,9,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8444 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8445 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 37 194 13 88 176 288 66 131 259), lower := (rows 37 194 13 88 176 288 66 128 256), losses := [] }

theorem u8445 : Upper (D 7) (R 7) [36,192,9,80,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8445 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8446 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 37 194 13 88 273 34 66 160 416), lower := (rows 37 194 13 88 273 34 66 128 256), losses := [] }

theorem u8446 : Upper (D 7) (R 7) [36,192,9,80,257,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8446 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8447 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 3, region := 130, targets := 32 }], pairs := [(1,0),(1,5),(2,1),(3,0)], upper := (rows 37 194 13 88 273 34 96 130 386), lower := (rows 37 194 13 88 273 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 32 97 128 256), good := (rows 101 192 77 92 349 96 96 128 256) }] }

theorem u8447 : Upper (D 7) (R 7) [36,192,9,80,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8447 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8448 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 13 88 273 34 192 162 290), lower := (rows 37 194 13 88 273 34 192 128 256), losses := [] }

theorem u8448 : Upper (D 7) (R 7) [36,192,9,80,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8448 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8449 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 5, region := 66, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(3,0)], upper := (rows 37 194 13 88 273 160 66 162 290), lower := (rows 37 194 13 88 273 160 66 128 256), losses := [{ target := 5, region := (rows 1 162 20 24 16 0 227 128 256), good := (rows 71 194 77 92 349 194 66 194 256) }] }

theorem u8449 : Upper (D 7) (R 7) [36,192,9,80,257,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8449 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8450 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 234, targets := 1 },{ cop := 3, region := 130, targets := 32 }], pairs := [(1,0),(1,5),(2,1),(3,0)], upper := (rows 37 194 13 88 273 160 96 130 258), lower := (rows 37 194 13 88 273 160 96 128 256), losses := [{ target := 1, region := (rows 1 0 20 24 16 162 227 128 256), good := (rows 101 224 77 92 349 224 96 224 256) }] }

theorem u8450 : Upper (D 7) (R 7) [36,192,9,80,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8450 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8451 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 304, targets := 64 }], pairs := [(1,0),(3,0),(4,0),(4,6)], upper := (rows 37 194 13 88 274 160 65 162 290), lower := (rows 37 194 13 88 274 160 65 128 256), losses := [] }

theorem u8451 : Upper (D 7) (R 7) [36,192,9,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8451 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8452 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 165, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 194 13 88 274 160 66 161 289), lower := (rows 37 194 13 88 274 160 66 128 256), losses := [] }

theorem u8452 : Upper (D 7) (R 7) [36,192,9,80,258,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8452 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8453 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 66, targets := 1 }], pairs := [(0,1),(1,0),(2,1),(3,0)], upper := (rows 37 194 13 88 274 160 96 131 259), lower := (rows 37 194 13 88 274 160 96 128 256), losses := [{ target := 0, region := (rows 0 162 4 24 16 162 243 128 256), good := (rows 102 226 76 88 378 226 98 226 256) },{ target := 1, region := (rows 17 0 28 24 16 162 243 128 256), good := (rows 101 224 77 93 381 224 96 224 256) }] }

theorem u8453 : Upper (D 7) (R 7) [36,192,9,80,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8453 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8454 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 13 88 304 34 65 130 386), lower := (rows 37 194 13 88 304 34 65 128 256), losses := [] }

theorem u8454 : Upper (D 7) (R 7) [36,192,9,80,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8454 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8455 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 400, targets := 66 },{ cop := 0, region := 194, targets := 32 },{ cop := 7, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(4,1),(4,6)], upper := (rows 37 194 13 88 304 34 66 129 385), lower := (rows 37 194 13 88 304 34 66 128 256), losses := [] }

theorem u8455 : Upper (D 7) (R 7) [36,192,9,80,288,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8455 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8456 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 37 194 13 88 304 34 192 131 259), lower := (rows 37 194 13 88 304 34 192 128 256), losses := [] }

theorem u8456 : Upper (D 7) (R 7) [36,192,9,80,288,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8456 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8457 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 77, targets := 130 }], pairs := [(0,1),(0,7),(2,1),(2,7)], upper := (rows 37 194 13 88 304 160 65 130 258), lower := (rows 37 194 13 88 304 160 65 128 256), losses := [] }

theorem u8457 : Upper (D 7) (R 7) [36,192,9,80,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8457 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8458 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 194, targets := 32 },{ cop := 5, region := 66, targets := 1 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 37 194 13 88 304 160 66 131 259), lower := (rows 37 194 13 88 304 160 66 128 256), losses := [{ target := 0, region := (rows 0 162 4 24 16 162 243 128 256), good := (rows 102 226 76 88 378 226 98 226 256) },{ target := 5, region := (rows 1 167 4 24 16 0 247 133 261), good := (rows 455 194 463 88 346 194 66 194 256) }] }

theorem u8458 : Upper (D 7) (R 7) [36,192,9,80,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8458 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8459 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 1, region := 304, targets := 64 }], pairs := [(1,0),(3,0),(4,0),(4,6)], upper := (rows 37 194 13 88 400 34 65 162 290), lower := (rows 37 194 13 88 400 34 65 128 256), losses := [] }

theorem u8459 : Upper (D 7) (R 7) [36,192,9,80,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8459 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u8459
end Delivery.IrregularNine14.P07

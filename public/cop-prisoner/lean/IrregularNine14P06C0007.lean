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

def b420 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 25 98 134 44 274 33 68 192 257), lower := (rows 25 98 134 44 274 33 68 192 256), losses := [] }

theorem u420 : Upper (D 6) (R 6) [24,96,130,36,258,1,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 37 }], pairs := [(4,0),(4,2),(4,5)], upper := (rows 25 98 134 44 336 33 68 129 258), lower := (rows 25 98 134 44 336 33 68 129 256), losses := [] }

theorem u421 : Upper (D 6) (R 6) [24,96,130,36,320,1,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b421 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 377, targets := 2 }], pairs := [(0,1),(3,1),(4,1)], upper := (rows 25 98 134 44 336 33 68 130 257), lower := (rows 25 98 134 44 336 33 68 130 256), losses := [] }

theorem u422 : Upper (D 6) (R 6) [24,96,130,36,320,1,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b422 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b423 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 333, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 131 261 14 50 96 68 160 320), lower := (rows 25 131 261 14 50 96 68 160 256), losses := [] }

theorem u423 : Upper (D 6) (R 6) [24,129,257,6,34,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b423 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 131 261 14 50 96 68 192 288), lower := (rows 25 131 261 14 50 96 68 192 256), losses := [] }

theorem u424 : Upper (D 6) (R 6) [24,129,257,6,34,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 341, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 131 261 42 84 36 66 160 320), lower := (rows 25 131 261 42 84 36 66 160 256), losses := [] }

theorem u425 : Upper (D 6) (R 6) [24,129,257,34,68,4,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b426 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 292, targets := 66 },{ cop := 0, region := 194, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 25 131 261 42 84 36 66 192 288), lower := (rows 25 131 261 42 84 36 66 192 256), losses := [] }

theorem u426 : Upper (D 6) (R 6) [24,129,257,34,68,4,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b426 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b427 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 333, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 25 131 262 13 50 96 68 160 320), lower := (rows 25 131 262 13 50 96 68 160 256), losses := [] }

theorem u427 : Upper (D 6) (R 6) [24,129,258,5,34,64,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b427 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 269, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 131 262 13 50 96 68 192 288), lower := (rows 25 131 262 13 50 96 68 192 256), losses := [] }

theorem u428 : Upper (D 6) (R 6) [24,129,258,5,34,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 139, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 134 262 42 52 96 65 129 320), lower := (rows 25 134 262 42 52 96 65 129 256), losses := [] }

theorem u429 : Upper (D 6) (R 6) [24,132,258,34,36,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b429 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 277, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 25 134 262 42 52 96 65 192 257), lower := (rows 25 134 262 42 52 96 65 192 256), losses := [] }

theorem u430 : Upper (D 6) (R 6) [24,132,258,34,36,64,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b430 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 341, targets := 32 }], pairs := [(0,5),(2,5),(4,5)], upper := (rows 25 134 262 42 84 33 65 160 320), lower := (rows 25 134 262 42 84 33 65 160 256), losses := [] }

theorem u431 : Upper (D 6) (R 6) [24,132,258,34,68,1,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b431 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b432 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 260, targets := 65 },{ cop := 4, region := 130, targets := 1 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 25 134 262 42 84 33 65 192 288), lower := (rows 25 134 262 42 84 33 65 192 256), losses := [] }

theorem u432 : Upper (D 6) (R 6) [24,132,258,34,68,1,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b433 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 171, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 25 134 262 42 84 33 96 129 320), lower := (rows 25 134 262 42 84 33 96 129 256), losses := [] }

theorem u433 : Upper (D 6) (R 6) [24,132,258,34,68,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b434 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 130, targets := 33 }], pairs := [(1,0),(1,5),(2,5)], upper := (rows 25 134 262 42 84 33 96 192 257), lower := (rows 25 134 262 42 84 33 96 192 256), losses := [{ target := 5, region := (rows 1 211 109 8 208 0 64 208 289), good := (rows 415 150 262 270 214 263 470 214 256) }] }

theorem u434 : Upper (D 6) (R 6) [24,132,258,34,68,1,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 340, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 25 134 292 11 112 34 68 129 320), lower := (rows 25 134 292 11 112 34 68 129 256), losses := [] }

theorem u435 : Upper (D 6) (R 6) [24,132,288,3,96,2,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b436 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 246, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 292 11 112 34 68 192 257), lower := (rows 25 134 292 11 112 34 68 192 256), losses := [] }

theorem u436 : Upper (D 6) (R 6) [24,132,288,3,96,2,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b437 : PairBound 9 := { available := 64, camps := [{ cop := 7, region := 374, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 25 134 292 13 82 34 96 129 320), lower := (rows 25 134 292 13 82 34 96 129 256), losses := [] }

theorem u437 : Upper (D 6) (R 6) [24,132,288,5,66,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b438 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 25 134 292 13 82 34 96 192 257), lower := (rows 25 134 292 13 82 34 96 192 256), losses := [] }

theorem u438 : Upper (D 6) (R 6) [24,132,288,5,66,2,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b438 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 260, targets := 65 }], pairs := [(1,0),(2,0),(2,6)], upper := (rows 25 134 292 42 84 96 65 129 258), lower := (rows 25 134 292 42 84 96 65 129 256), losses := [{ target := 0, region := (rows 0 130 13 8 80 112 64 128 394), good := (rows 316 390 292 302 116 112 116 390 256) }] }

theorem u439 : Upper (D 6) (R 6) [24,132,288,34,68,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b439 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b440 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 138, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 25 134 292 42 84 96 65 130 257), lower := (rows 25 134 292 42 84 96 65 130 256), losses := [] }

theorem u440 : Upper (D 6) (R 6) [24,132,288,34,68,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b440 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 152, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 67 44 25 208 288 68 130 260), lower := (rows 35 67 44 25 208 288 68 130 256), losses := [] }

theorem u441 : Upper (D 6) (R 6) [34,65,40,17,192,256,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b441 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 220, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 25 208 288 68 132 258), lower := (rows 35 67 44 25 208 288 68 132 256), losses := [] }

theorem u442 : Upper (D 6) (R 6) [34,65,40,17,192,256,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b442 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b443 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 152, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 67 44 88 145 288 68 130 260), lower := (rows 35 67 44 88 145 288 68 130 256), losses := [] }

theorem u443 : Upper (D 6) (R 6) [34,65,40,80,129,256,4,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b443 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b444 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 220, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 88 145 288 68 132 258), lower := (rows 35 67 44 88 145 288 68 132 256), losses := [] }

theorem u444 : Upper (D 6) (R 6) [34,65,40,80,129,256,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b444 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b445 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 152, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 67 44 88 146 288 68 129 260), lower := (rows 35 67 44 88 146 288 68 129 256), losses := [] }

theorem u445 : Upper (D 6) (R 6) [34,65,40,80,130,256,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b445 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b446 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 220, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 35 67 44 88 146 288 68 132 257), lower := (rows 35 67 44 88 146 288 68 132 256), losses := [] }

theorem u446 : Upper (D 6) (R 6) [34,65,40,80,130,256,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b446 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b447 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 156, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 44 137 22 288 68 144 320), lower := (rows 35 67 44 137 22 288 68 144 256), losses := [] }

theorem u447 : Upper (D 6) (R 6) [34,65,40,129,6,256,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b447 [(5,8),(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 67 44 137 22 288 68 192 272), lower := (rows 35 67 44 137 22 288 68 192 256), losses := [] }

theorem u448 : Upper (D 6) (R 6) [34,65,40,129,6,256,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b448 [(5,8)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 132, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 35 70 134 25 276 40 96 129 320), lower := (rows 35 70 134 25 276 40 96 129 256), losses := [] }

theorem u449 : Upper (D 6) (R 6) [34,68,130,17,260,8,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b449 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 134, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 134 25 276 40 96 192 257), lower := (rows 35 70 134 25 276 40 96 192 256), losses := [] }

theorem u450 : Upper (D 6) (R 6) [34,68,130,17,260,8,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b450 [(5,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 280, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 70 140 26 276 33 96 129 320), lower := (rows 35 70 140 26 276 33 96 129 256), losses := [] }

theorem u451 : Upper (D 6) (R 6) [34,68,136,18,260,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 70 140 26 276 33 96 192 257), lower := (rows 35 70 140 26 276 33 96 192 256), losses := [] }

theorem u452 : Upper (D 6) (R 6) [34,68,136,18,260,1,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b452 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 202, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 84 138 304 36 65 129 260), lower := (rows 35 74 84 138 304 36 65 129 256), losses := [] }

theorem u453 : Upper (D 6) (R 6) [34,72,80,130,288,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b454 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 2, region := 138, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 35 74 84 138 304 36 65 132 257), lower := (rows 35 74 84 138 304 36 65 132 256), losses := [] }

theorem u454 : Upper (D 6) (R 6) [34,72,80,130,288,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b454 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b455 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 74 100 140 276 48 65 129 258), lower := (rows 35 74 100 140 276 48 65 129 256), losses := [] }

theorem u455 : Upper (D 6) (R 6) [34,72,96,132,260,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b455 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b456 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 138, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 74 100 140 276 48 65 130 257), lower := (rows 35 74 100 140 276 48 65 130 256), losses := [] }

theorem u456 : Upper (D 6) (R 6) [34,72,96,132,260,16,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b456 [(5,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b457 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 308, targets := 1 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 74 100 152 274 36 65 129 260), lower := (rows 35 74 100 152 274 36 65 129 256), losses := [] }

theorem u457 : Upper (D 6) (R 6) [34,72,96,144,258,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 36 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,1),(4,2),(4,5)], upper := (rows 35 74 100 152 274 36 65 132 257), lower := (rows 35 74 100 152 274 36 65 132 256), losses := [] }

theorem u458 : Upper (D 6) (R 6) [34,72,96,144,258,4,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b459 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 308, targets := 1 },{ cop := 0, region := 68, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 74 100 152 276 36 65 129 258), lower := (rows 35 74 100 152 276 36 65 129 256), losses := [] }

theorem u459 : Upper (D 6) (R 6) [34,72,96,144,260,4,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b460 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 1, region := 36, targets := 1 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 35 74 100 152 276 36 65 130 257), lower := (rows 35 74 100 152 276 36 65 130 256), losses := [] }

theorem u460 : Upper (D 6) (R 6) [34,72,96,144,260,4,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 331, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 74 196 266 21 36 65 144 288), lower := (rows 35 74 196 266 21 36 65 144 256), losses := [] }

theorem u461 : Upper (D 6) (R 6) [34,72,192,258,5,4,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b461 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 330, targets := 36 }], pairs := [(1,2),(1,5),(3,2)], upper := (rows 35 74 196 266 21 36 65 160 272), lower := (rows 35 74 196 266 21 36 65 160 256), losses := [] }

theorem u462 : Upper (D 6) (R 6) [34,72,192,258,5,4,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b463 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 3, region := 100, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 25 274 96 68 132 320), lower := (rows 35 131 44 25 274 96 68 132 256), losses := [] }

theorem u463 : Upper (D 6) (R 6) [34,129,40,17,258,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b464 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 131 44 25 274 96 68 192 260), lower := (rows 35 131 44 25 274 96 68 192 256), losses := [] }

theorem u464 : Upper (D 6) (R 6) [34,129,40,17,258,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 3, region := 100, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 26 273 96 68 132 320), lower := (rows 35 131 44 26 273 96 68 132 256), losses := [] }

theorem u465 : Upper (D 6) (R 6) [34,129,40,18,257,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 131 44 26 273 96 68 192 260), lower := (rows 35 131 44 26 273 96 68 192 256), losses := [] }

theorem u466 : Upper (D 6) (R 6) [34,129,40,18,257,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 147, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 265 22 96 68 144 320), lower := (rows 35 131 44 265 22 96 68 144 256), losses := [] }

theorem u467 : Upper (D 6) (R 6) [34,129,40,257,6,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b467 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b468 : PairBound 9 := { available := 16, camps := [{ cop := 0, region := 284, targets := 64 }], pairs := [(2,6),(3,6),(4,6)], upper := (rows 35 131 44 265 22 96 68 192 272), lower := (rows 35 131 44 265 22 96 68 192 256), losses := [] }

theorem u468 : Upper (D 6) (R 6) [34,129,40,257,6,64,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b469 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 131, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 35 131 44 265 22 96 80 132 320), lower := (rows 35 131 44 265 22 96 80 132 256), losses := [] }

theorem u469 : Upper (D 6) (R 6) [34,129,40,257,6,64,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b469 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b470 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 268, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 35 131 44 265 22 96 80 192 260), lower := (rows 35 131 44 265 22 96 80 192 256), losses := [] }

theorem u470 : Upper (D 6) (R 6) [34,129,40,257,6,64,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b470 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b471 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 131, targets := 64 },{ cop := 3, region := 100, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 44 266 81 96 68 132 272), lower := (rows 35 131 44 266 81 96 68 132 256), losses := [] }

theorem u471 : Upper (D 6) (R 6) [34,129,40,258,65,64,4,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b472 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 147, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 44 266 81 96 68 144 260), lower := (rows 35 131 44 266 81 96 68 144 256), losses := [] }

theorem u472 : Upper (D 6) (R 6) [34,129,40,258,65,64,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b472 [(7,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 272, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 131 70 28 273 96 72 132 288), lower := (rows 35 131 70 28 273 96 72 132 256), losses := [] }

theorem u473 : Upper (D 6) (R 6) [34,129,66,20,257,64,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b473 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b474 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 131, targets := 68 }], pairs := [(0,2),(0,6)], upper := (rows 35 131 70 28 273 96 72 160 260), lower := (rows 35 131 70 28 273 96 72 160 256), losses := [] }

theorem u474 : Upper (D 6) (R 6) [34,129,66,20,257,64,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b474 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b475 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 35 131 70 28 304 96 72 129 260), lower := (rows 35 131 70 28 304 96 72 129 256), losses := [] }

theorem u475 : Upper (D 6) (R 6) [34,129,66,20,288,64,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b475 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 35 131 70 28 304 96 72 132 257), lower := (rows 35 131 70 28 304 96 72 132 256), losses := [] }

theorem u476 : Upper (D 6) (R 6) [34,129,66,20,288,64,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b476 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 344, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 35 131 70 56 273 36 72 132 320), lower := (rows 35 131 70 56 273 36 72 132 256), losses := [] }

theorem u477 : Upper (D 6) (R 6) [34,129,66,48,257,4,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b477 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b478 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 313, targets := 64 }], pairs := [(0,6),(3,6)], upper := (rows 35 131 70 56 273 36 72 192 260), lower := (rows 35 131 70 56 273 36 72 192 256), losses := [] }

theorem u478 : Upper (D 6) (R 6) [34,129,66,48,257,4,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b478 [(6,3)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b479 : PairBound 9 := { available := 32, camps := [{ cop := 7, region := 371, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 35 131 76 13 274 96 80 132 288), lower := (rows 35 131 76 13 274 96 80 132 256), losses := [] }

theorem u479 : Upper (D 6) (R 6) [34,129,72,5,258,64,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b479 [(6,4)]
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P06

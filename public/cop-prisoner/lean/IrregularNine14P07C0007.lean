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

def b420 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 130, targets := 33 },{ cop := 0, region := 144, targets := 1 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 194 13 88 176 288 65 130 260), lower := (rows 35 194 13 88 176 288 65 130 256), losses := [] }

theorem u420 : Upper (D 7) (R 7) [34,192,9,80,160,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b420 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 220, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 194 13 88 176 288 65 132 258), lower := (rows 35 194 13 88 176 288 65 132 256), losses := [] }

theorem u421 : Upper (D 7) (R 7) [34,192,9,80,160,256,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b421 [(5,8),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 280, targets := 33 }], pairs := [(3,0),(3,5),(4,0)], upper := (rows 35 194 13 88 400 36 96 129 258), lower := (rows 35 194 13 88 400 36 96 129 256), losses := [] }

theorem u422 : Upper (D 7) (R 7) [34,192,9,80,384,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b422 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b423 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 400, targets := 96 },{ cop := 3, region := 130, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 35 194 13 88 400 36 96 130 257), lower := (rows 35 194 13 88 400 36 96 130 256), losses := [] }

theorem u423 : Upper (D 7) (R 7) [34,192,9,80,384,4,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b423 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 284, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 76 152 274 33 96 129 260), lower := (rows 35 194 76 152 274 33 96 129 256), losses := [] }

theorem u424 : Upper (D 7) (R 7) [34,192,72,144,258,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b424 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 35 194 76 152 274 33 96 132 257), lower := (rows 35 194 76 152 274 33 96 132 256), losses := [] }

theorem u425 : Upper (D 7) (R 7) [34,192,72,144,258,1,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b425 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b426 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 284, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5)], upper := (rows 35 194 76 152 276 33 96 129 258), lower := (rows 35 194 76 152 276 33 96 129 256), losses := [] }

theorem u426 : Upper (D 7) (R 7) [34,192,72,144,260,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b426 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b427 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 130, targets := 33 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(1,0),(1,5)], upper := (rows 35 194 76 152 276 33 96 130 257), lower := (rows 35 194 76 152 276 33 96 130 256), losses := [] }

theorem u427 : Upper (D 7) (R 7) [34,192,72,144,260,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b427 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 259 13 74 148 160 80 160 320), lower := (rows 35 259 13 74 148 160 80 160 256), losses := [] }

theorem u428 : Upper (D 7) (R 7) [34,257,9,66,132,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b428 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 259, targets := 192 }], pairs := [(0,6),(0,7),(1,6)], upper := (rows 35 259 13 74 148 160 80 192 288), lower := (rows 35 259 13 74 148 160 80 192 256), losses := [] }

theorem u429 : Upper (D 7) (R 7) [34,257,9,66,132,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b429 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 64, camps := [{ cop := 8, region := 179, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 13 88 146 160 68 160 320), lower := (rows 35 259 13 88 146 160 68 160 256), losses := [] }

theorem u430 : Upper (D 7) (R 7) [34,257,9,80,130,128,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b430 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 259 13 88 146 160 68 192 288), lower := (rows 35 259 13 88 146 160 68 192 256), losses := [] }

theorem u431 : Upper (D 7) (R 7) [34,257,9,80,130,128,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b431 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b432 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 35 259 14 73 148 96 192 144 288), lower := (rows 35 259 14 73 148 96 192 144 256), losses := [] }

theorem u432 : Upper (D 7) (R 7) [34,257,10,65,132,64,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b432 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b433 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 240, targets := 3 },{ cop := 0, region := 200, targets := 2 }], pairs := [(1,6),(3,1),(4,0),(4,1)], upper := (rows 35 259 14 73 148 96 192 160 272), lower := (rows 35 259 14 73 148 96 192 160 256), losses := [{ target := 6, region := (rows 1 10 12 8 24 32 0 161 284), good := (rows 163 387 286 415 404 160 128 160 256) }] }

theorem u433 : Upper (D 7) (R 7) [34,257,10,65,132,64,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b433 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b434 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 262, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 259 14 73 148 160 80 160 320), lower := (rows 35 259 14 73 148 160 80 160 256), losses := [] }

theorem u434 : Upper (D 7) (R 7) [34,257,10,65,132,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b434 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 259, targets := 192 }], pairs := [(0,6),(0,7),(1,6)], upper := (rows 35 259 14 73 148 160 80 192 288), lower := (rows 35 259 14 73 148 160 80 192 256), losses := [] }

theorem u435 : Upper (D 7) (R 7) [34,257,10,65,132,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b435 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b436 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 259, targets := 192 }], pairs := [(0,6),(0,7),(1,6)], upper := (rows 35 259 14 73 176 96 192 132 272), lower := (rows 35 259 14 73 176 96 192 132 256), losses := [] }

theorem u436 : Upper (D 7) (R 7) [34,257,10,65,160,64,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b436 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b437 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 262, targets := 96 }], pairs := [(1,5),(1,6),(2,5)], upper := (rows 35 259 14 73 176 96 192 144 260), lower := (rows 35 259 14 73 176 96 192 144 256), losses := [] }

theorem u437 : Upper (D 7) (R 7) [34,257,10,65,160,64,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b437 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b438 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 259 14 76 145 160 80 160 320), lower := (rows 35 259 14 76 145 160 80 160 256), losses := [] }

theorem u438 : Upper (D 7) (R 7) [34,257,10,68,129,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b438 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 259 14 76 145 160 80 192 288), lower := (rows 35 259 14 76 145 160 80 192 256), losses := [] }

theorem u439 : Upper (D 7) (R 7) [34,257,10,68,129,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b439 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b440 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 259 14 88 145 160 68 160 320), lower := (rows 35 259 14 88 145 160 68 160 256), losses := [] }

theorem u440 : Upper (D 7) (R 7) [34,257,10,80,129,128,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b440 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 259 14 88 145 160 68 192 288), lower := (rows 35 259 14 88 145 160 68 192 256), losses := [] }

theorem u441 : Upper (D 7) (R 7) [34,257,10,80,129,128,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b441 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 259 28 73 146 96 192 132 288), lower := (rows 35 259 28 73 146 96 192 132 256), losses := [] }

theorem u442 : Upper (D 7) (R 7) [34,257,24,65,130,64,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b442 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b443 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 144, targets := 1 },{ cop := 0, region := 200, targets := 2 },{ cop := 0, region := 144, targets := 64 }], pairs := [(2,0),(3,1),(4,0),(4,6)], upper := (rows 35 259 28 73 146 96 192 160 260), lower := (rows 35 259 28 73 146 96 192 160 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 511 511 511 268), good := (rows 242 498 508 508 242 224 224 224 480) }] }

theorem u443 : Upper (D 7) (R 7) [34,257,24,65,130,64,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b443 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b444 : PairBound 9 := { available := 64, camps := [{ cop := 8, region := 179, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 35 259 28 73 146 160 68 160 320), lower := (rows 35 259 28 73 146 160 68 160 256), losses := [] }

theorem u444 : Upper (D 7) (R 7) [34,257,24,65,130,128,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b444 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b445 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 259 28 73 146 160 68 192 288), lower := (rows 35 259 28 73 146 160 68 192 256), losses := [] }

theorem u445 : Upper (D 7) (R 7) [34,257,24,65,130,128,4,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b445 [(6,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b446 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 35 259 44 74 145 48 192 132 320), lower := (rows 35 259 44 74 145 48 192 132 256), losses := [] }

theorem u446 : Upper (D 7) (R 7) [34,257,40,66,129,16,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b446 [(5,4),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b447 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 259, targets := 192 }], pairs := [(0,6),(0,7),(1,6)], upper := (rows 35 259 44 74 145 48 192 192 260), lower := (rows 35 259 44 74 145 48 192 192 256), losses := [] }

theorem u447 : Upper (D 7) (R 7) [34,257,40,66,129,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b447 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 322, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 35 259 44 74 145 160 80 132 320), lower := (rows 35 259 44 74 145 160 80 132 256), losses := [] }

theorem u448 : Upper (D 7) (R 7) [34,257,40,66,129,128,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b448 [(6,4),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 259, targets := 192 }], pairs := [(0,6),(0,7),(1,6)], upper := (rows 35 259 44 74 145 160 80 192 260), lower := (rows 35 259 44 74 145 160 80 192 256), losses := [] }

theorem u449 : Upper (D 7) (R 7) [34,257,40,66,129,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b449 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 181, targets := 64 }], pairs := [(0,6),(2,6),(4,6)], upper := (rows 35 259 44 74 148 160 80 129 320), lower := (rows 35 259 44 74 148 160 80 129 256), losses := [] }

theorem u450 : Upper (D 7) (R 7) [34,257,40,66,132,128,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b450 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 259, targets := 192 }], pairs := [(0,6),(0,7),(1,6)], upper := (rows 35 259 44 74 148 160 80 192 257), lower := (rows 35 259 44 74 148 160 80 192 256), losses := [] }

theorem u451 : Upper (D 7) (R 7) [34,257,40,66,132,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b451 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 291, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 259 69 74 148 48 192 136 288), lower := (rows 35 259 69 74 148 48 192 136 256), losses := [] }

theorem u452 : Upper (D 7) (R 7) [34,257,65,66,132,16,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b452 [(5,4),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 266, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 35 259 69 74 148 48 192 160 264), lower := (rows 35 259 69 74 148 48 192 160 256), losses := [] }

theorem u453 : Upper (D 7) (R 7) [34,257,65,66,132,16,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b453 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b454 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 259, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 259 69 74 148 160 80 136 288), lower := (rows 35 259 69 74 148 160 80 136 256), losses := [] }

theorem u454 : Upper (D 7) (R 7) [34,257,65,66,132,128,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b454 [(6,4),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b455 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 266, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 35 259 69 74 148 160 80 160 264), lower := (rows 35 259 69 74 148 160 80 160 256), losses := [] }

theorem u455 : Upper (D 7) (R 7) [34,257,65,66,132,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b455 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b456 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 291, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 259 69 74 152 48 192 132 288), lower := (rows 35 259 69 74 152 48 192 132 256), losses := [] }

theorem u456 : Upper (D 7) (R 7) [34,257,65,66,136,16,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b456 [(5,4),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b457 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 266, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 35 259 69 74 152 48 192 160 260), lower := (rows 35 259 69 74 152 48 192 160 256), losses := [] }

theorem u457 : Upper (D 7) (R 7) [34,257,65,66,136,16,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b457 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 259, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 259 69 74 152 160 80 132 288), lower := (rows 35 259 69 74 152 160 80 132 256), losses := [] }

theorem u458 : Upper (D 7) (R 7) [34,257,65,66,136,128,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b458 [(6,4),(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b459 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 266, targets := 160 }], pairs := [(1,5),(1,7),(3,5)], upper := (rows 35 259 69 74 152 160 80 160 260), lower := (rows 35 259 69 74 152 160 80 160 256), losses := [] }

theorem u459 : Upper (D 7) (R 7) [34,257,65,66,136,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b459 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b460 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 160 }], pairs := [(1,5),(1,7),(2,5)], upper := (rows 35 262 13 74 145 160 80 160 320), lower := (rows 35 262 13 74 145 160 80 160 256), losses := [] }

theorem u460 : Upper (D 7) (R 7) [34,260,9,66,129,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b460 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 262 13 74 145 160 80 192 288), lower := (rows 35 262 13 74 145 160 80 192 256), losses := [] }

theorem u461 : Upper (D 7) (R 7) [34,260,9,66,129,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b461 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 },{ cop := 4, region := 302, targets := 1 }], pairs := [(1,0),(2,5),(3,5),(4,5)], upper := (rows 35 262 76 26 208 160 65 129 288), lower := (rows 35 262 76 26 208 160 65 129 256), losses := [] }

theorem u462 : Upper (D 7) (R 7) [34,260,72,18,192,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b462 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b463 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 176, targets := 3 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 35 262 76 26 208 160 65 160 257), lower := (rows 35 262 76 26 208 160 65 160 256), losses := [] }

theorem u463 : Upper (D 7) (R 7) [34,260,72,18,192,128,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b463 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b464 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 262 76 138 208 48 65 129 288), lower := (rows 35 262 76 138 208 48 65 129 256), losses := [] }

theorem u464 : Upper (D 7) (R 7) [34,260,72,130,192,16,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b464 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 176, targets := 3 },{ cop := 0, region := 136, targets := 1 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 35 262 76 138 208 48 65 160 257), lower := (rows 35 262 76 138 208 48 65 160 256), losses := [] }

theorem u465 : Upper (D 7) (R 7) [34,260,72,130,192,16,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b465 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 334, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 262 196 88 176 33 66 129 264), lower := (rows 35 262 196 88 176 33 66 129 256), losses := [] }

theorem u466 : Upper (D 7) (R 7) [34,260,192,80,160,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b466 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 220, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 35 262 196 88 176 33 66 136 257), lower := (rows 35 262 196 88 176 33 66 136 256), losses := [] }

theorem u467 : Upper (D 7) (R 7) [34,260,192,80,160,1,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b467 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b468 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 322 13 26 208 160 65 132 288), lower := (rows 35 322 13 26 208 160 65 132 256), losses := [] }

theorem u468 : Upper (D 7) (R 7) [34,320,9,18,192,128,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b468 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b469 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 184, targets := 1 },{ cop := 2, region := 322, targets := 160 }], pairs := [(1,5),(1,7),(3,0),(4,0)], upper := (rows 35 322 13 26 208 160 65 160 260), lower := (rows 35 322 13 26 208 160 65 160 256), losses := [] }

theorem u469 : Upper (D 7) (R 7) [34,320,9,18,192,128,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b469 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b470 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 322 13 76 146 160 80 129 288), lower := (rows 35 322 13 76 146 160 80 129 256), losses := [] }

theorem u470 : Upper (D 7) (R 7) [34,320,9,68,130,128,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b470 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b471 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 177, targets := 64 },{ cop := 8, region := 242, targets := 1 }], pairs := [(0,6),(1,0),(4,6)], upper := (rows 35 322 13 76 146 160 80 160 257), lower := (rows 35 322 13 76 146 160 80 160 256), losses := [] }

theorem u471 : Upper (D 7) (R 7) [34,320,9,68,130,128,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b471 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b472 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 322 13 88 146 160 65 132 288), lower := (rows 35 322 13 88 146 160 65 132 256), losses := [] }

theorem u472 : Upper (D 7) (R 7) [34,320,9,80,130,128,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b472 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 184, targets := 1 },{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6),(3,0),(4,0),(4,6)], upper := (rows 35 322 13 88 146 160 65 160 260), lower := (rows 35 322 13 88 146 160 65 160 256), losses := [] }

theorem u473 : Upper (D 7) (R 7) [34,320,9,80,130,128,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b473 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b474 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 322 13 200 22 160 65 144 288), lower := (rows 35 322 13 200 22 160 65 144 256), losses := [] }

theorem u474 : Upper (D 7) (R 7) [34,320,9,192,6,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b474 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b475 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 338, targets := 160 }], pairs := [(1,5),(1,7),(4,5),(4,7)], upper := (rows 35 322 13 200 22 160 65 160 272), lower := (rows 35 322 13 200 22 160 65 160 256), losses := [] }

theorem u475 : Upper (D 7) (R 7) [34,320,9,192,6,128,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b475 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 274, targets := 33 }], pairs := [(1,0),(1,5),(4,0)], upper := (rows 35 322 13 200 146 36 96 129 272), lower := (rows 35 322 13 200 146 36 96 129 256), losses := [] }

theorem u476 : Upper (D 7) (R 7) [34,320,9,192,130,4,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b476 [(5,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 152, targets := 33 }], pairs := [(3,0),(3,5)], upper := (rows 35 322 13 200 146 36 96 144 257), lower := (rows 35 322 13 200 146 36 96 144 256), losses := [] }

theorem u477 : Upper (D 7) (R 7) [34,320,9,192,130,4,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b477 [(5,2),(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b478 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 220, targets := 32 }], pairs := [(2,5),(3,5),(4,5)], upper := (rows 35 322 14 152 81 33 192 132 288), lower := (rows 35 322 14 152 81 33 192 132 256), losses := [] }

theorem u478 : Upper (D 7) (R 7) [34,320,10,144,65,1,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b478 [(7,2)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b479 : PairBound 9 := { available := 4, camps := [{ cop := 3, region := 326, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 322 14 152 81 33 192 160 260), lower := (rows 35 322 14 152 81 33 192 160 256), losses := [] }

theorem u479 : Upper (D 7) (R 7) [34,320,10,144,65,1,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b479 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P07

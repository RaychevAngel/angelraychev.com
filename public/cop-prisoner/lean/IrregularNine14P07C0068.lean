import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0005

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4080 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 80, targets := 34 },{ cop := 4, region := 298, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,5)], upper := (rows 13 98 133 296 81 34 192 146 274), lower := (rows 13 98 133 296 81 34 192 128 256), losses := [] }

theorem u4080 : Upper (D 7) (R 7) [12,96,129,288,65,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4080 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4081 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 4, region := 426, targets := 1 }], pairs := [(1,0),(1,7),(3,0),(4,7)], upper := (rows 13 98 133 296 81 160 66 146 274), lower := (rows 13 98 133 296 81 160 66 128 256), losses := [{ target := 7, region := (rows 1 42 4 8 21 32 107 0 257), good := (rows 351 98 341 362 337 98 66 0 256) }] }

theorem u4081 : Upper (D 7) (R 7) [12,96,129,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4081 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4082 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 13 98 133 296 81 160 80 130 258), lower := (rows 13 98 133 296 81 160 80 128 256), losses := [] }

theorem u4082 : Upper (D 7) (R 7) [12,96,129,288,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4082 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4083 : PairBound 9 := { available := 80, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 13 98 133 296 146 34 65 208 336), lower := (rows 13 98 133 296 146 34 65 128 256), losses := [] }

theorem u4083 : Upper (D 7) (R 7) [12,96,129,288,130,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4083 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4084 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 98 133 296 146 34 80 193 321), lower := (rows 13 98 133 296 146 34 80 128 256), losses := [] }

theorem u4084 : Upper (D 7) (R 7) [12,96,129,288,130,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4084 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4085 : PairBound 9 := { available := 66, camps := [{ cop := 6, region := 442, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 13 98 133 296 146 48 65 194 322), lower := (rows 13 98 133 296 146 48 65 128 256), losses := [] }

theorem u4085 : Upper (D 7) (R 7) [12,96,129,288,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4085 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4086 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 2 }], pairs := [(0,1),(2,1),(3,1)], upper := (rows 13 98 133 296 146 48 66 193 321), lower := (rows 13 98 133 296 146 48 66 128 256), losses := [] }

theorem u4086 : Upper (D 7) (R 7) [12,96,129,288,130,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4086 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4087 : PairBound 9 := { available := 18, camps := [{ cop := 6, region := 442, targets := 1 },{ cop := 2, region := 80, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 13 98 133 296 208 34 65 146 274), lower := (rows 13 98 133 296 208 34 65 128 256), losses := [] }

theorem u4087 : Upper (D 7) (R 7) [12,96,129,288,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4087 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4088 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 413, targets := 2 }], pairs := [(0,1),(2,1),(3,1),(4,1)], upper := (rows 13 98 133 296 208 34 66 145 273), lower := (rows 13 98 133 296 208 34 66 128 256), losses := [] }

theorem u4088 : Upper (D 7) (R 7) [12,96,129,288,192,2,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4088 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4089 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 133 296 208 34 80 131 259), lower := (rows 13 98 133 296 208 34 80 128 256), losses := [] }

theorem u4089 : Upper (D 7) (R 7) [12,96,129,288,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4089 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4090 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 6, region := 290, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 13 98 134 152 49 288 65 194 322), lower := (rows 13 98 134 152 49 288 65 128 256), losses := [] }

theorem u4090 : Upper (D 7) (R 7) [12,96,130,144,33,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4090 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4091 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 13 98 134 152 49 288 66 193 321), lower := (rows 13 98 134 152 49 288 66 128 256), losses := [] }

theorem u4091 : Upper (D 7) (R 7) [12,96,130,144,33,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4091 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4092 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(4,7)], upper := (rows 13 98 134 152 273 33 66 224 352), lower := (rows 13 98 134 152 273 33 66 128 256), losses := [] }

theorem u4092 : Upper (D 7) (R 7) [12,96,130,144,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4092 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4093 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 134 152 273 34 96 193 321), lower := (rows 13 98 134 152 273 34 96 128 256), losses := [] }

theorem u4093 : Upper (D 7) (R 7) [12,96,130,144,257,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4093 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4094 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7),(2,0),(3,0),(4,0)], upper := (rows 13 98 134 152 274 33 65 224 352), lower := (rows 13 98 134 152 274 33 65 128 256), losses := [] }

theorem u4094 : Upper (D 7) (R 7) [12,96,130,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4094 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4095 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 134 152 274 33 96 193 321), lower := (rows 13 98 134 152 274 33 96 128 256), losses := [] }

theorem u4095 : Upper (D 7) (R 7) [12,96,130,144,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4095 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4096 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7),(2,0),(3,0),(4,0)], upper := (rows 13 98 134 152 304 33 65 194 322), lower := (rows 13 98 134 152 304 33 65 128 256), losses := [] }

theorem u4096 : Upper (D 7) (R 7) [12,96,130,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4096 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4097 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(4,7)], upper := (rows 13 98 134 152 304 33 66 193 321), lower := (rows 13 98 134 152 304 33 66 128 256), losses := [{ target := 0, region := (rows 0 50 12 8 16 32 126 128 256), good := (rows 76 98 198 222 370 98 66 128 256) }] }

theorem u4097 : Upper (D 7) (R 7) [12,96,130,144,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4097 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4098 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 6, region := 34, targets := 1 }], pairs := [(0,1),(1,0),(1,7),(4,7)], upper := (rows 13 98 134 152 304 34 65 193 321), lower := (rows 13 98 134 152 304 34 65 128 256), losses := [{ target := 1, region := (rows 5 0 4 14 18 32 69 197 325), good := (rows 461 504 477 152 304 56 449 128 256) }] }

theorem u4098 : Upper (D 7) (R 7) [12,96,130,144,288,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4098 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4099 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 430, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 13 98 134 168 81 288 65 146 274), lower := (rows 13 98 134 168 81 288 65 128 256), losses := [] }

theorem u4099 : Upper (D 7) (R 7) [12,96,130,160,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4099 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4100 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 13 98 134 168 81 288 66 145 273), lower := (rows 13 98 134 168 81 288 66 128 256), losses := [] }

theorem u4100 : Upper (D 7) (R 7) [12,96,130,160,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4100 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4101 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 13 98 134 168 81 288 80 131 259), lower := (rows 13 98 134 168 81 288 80 128 256), losses := [] }

theorem u4101 : Upper (D 7) (R 7) [12,96,130,160,65,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4101 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4102 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 1, region := 132, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 13 98 134 168 273 48 65 194 322), lower := (rows 13 98 134 168 273 48 65 128 256), losses := [] }

theorem u4102 : Upper (D 7) (R 7) [12,96,130,160,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4102 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4103 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 13 98 134 168 273 48 66 193 321), lower := (rows 13 98 134 168 273 48 66 128 256), losses := [] }

theorem u4103 : Upper (D 7) (R 7) [12,96,130,160,257,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4103 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4104 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 370, targets := 128 }], pairs := [(0,1),(1,7),(4,7)], upper := (rows 13 98 134 168 274 48 65 193 321), lower := (rows 13 98 134 168 274 48 65 128 256), losses := [{ target := 1, region := (rows 5 0 4 10 16 48 69 197 325), good := (rows 461 488 461 168 312 48 449 128 256) }] }

theorem u4104 : Upper (D 7) (R 7) [12,96,130,160,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4104 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4105 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 13 98 134 265 19 48 192 224 352), lower := (rows 13 98 134 265 19 48 192 128 256), losses := [] }

theorem u4105 : Upper (D 7) (R 7) [12,96,130,257,3,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4105 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4106 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 265 19 96 192 176 304), lower := (rows 13 98 134 265 19 96 192 128 256), losses := [] }

theorem u4106 : Upper (D 7) (R 7) [12,96,130,257,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4107 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 396, targets := 1 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7),(2,0),(3,0)], upper := (rows 13 98 134 266 145 33 80 224 352), lower := (rows 13 98 134 266 145 33 80 128 256), losses := [] }

theorem u4107 : Upper (D 7) (R 7) [12,96,130,258,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4107 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4108 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 134 266 145 33 96 208 336), lower := (rows 13 98 134 266 145 33 96 128 256), losses := [] }

theorem u4108 : Upper (D 7) (R 7) [12,96,130,258,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4108 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4109 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 240, targets := 2 }], pairs := [(2,0),(3,0),(4,0),(4,1)], upper := (rows 13 98 134 266 176 33 65 208 336), lower := (rows 13 98 134 266 176 33 65 128 256), losses := [] }

theorem u4109 : Upper (D 7) (R 7) [12,96,130,258,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4109 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4110 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 397, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 13 98 134 266 176 33 80 193 321), lower := (rows 13 98 134 266 176 33 80 128 256), losses := [] }

theorem u4110 : Upper (D 7) (R 7) [12,96,130,258,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4110 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4111 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 198, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(3,1)], upper := (rows 13 98 134 280 19 33 192 224 352), lower := (rows 13 98 134 280 19 33 192 128 256), losses := [{ target := 0, region := (rows 0 34 54 24 16 32 246 162 290), good := (rows 76 486 454 348 478 486 192 192 256) }] }

theorem u4111 : Upper (D 7) (R 7) [12,96,130,272,3,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4112 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6),(2,6),(3,6),(4,6)], upper := (rows 13 98 134 280 19 96 192 161 289), lower := (rows 13 98 134 280 19 96 192 128 256), losses := [] }

theorem u4112 : Upper (D 7) (R 7) [12,96,130,272,3,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4112 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4113 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 362, targets := 128 },{ cop := 5, region := 198, targets := 1 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 134 280 145 33 66 224 352), lower := (rows 13 98 134 280 145 33 66 128 256), losses := [] }

theorem u4113 : Upper (D 7) (R 7) [12,96,130,272,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4113 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4114 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 134 280 145 34 96 193 321), lower := (rows 13 98 134 280 145 34 96 128 256), losses := [] }

theorem u4114 : Upper (D 7) (R 7) [12,96,130,272,129,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4115 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7),(2,0),(3,0),(4,0)], upper := (rows 13 98 134 280 176 33 65 194 322), lower := (rows 13 98 134 280 176 33 65 128 256), losses := [] }

theorem u4115 : Upper (D 7) (R 7) [12,96,130,272,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4116 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 70, targets := 1 },{ cop := 0, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(2,0),(3,7)], upper := (rows 13 98 134 280 176 33 66 193 321), lower := (rows 13 98 134 280 176 33 66 128 256), losses := [{ target := 7, region := (rows 1 51 4 24 16 33 127 0 289), good := (rows 367 354 70 346 378 355 66 0 256) }] }

theorem u4116 : Upper (D 7) (R 7) [12,96,130,272,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4117 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 132, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 13 98 134 296 19 33 80 192 448), lower := (rows 13 98 134 296 19 33 80 128 256), losses := [] }

theorem u4117 : Upper (D 7) (R 7) [12,96,130,288,3,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4117 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4118 : Route 9 := (fun mask => (mask,id))

def c4118 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4118 : Upper (D 7) (R 7) [12,96,130,288,3,1,128] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,3,1,128] 13 (by decide) (choices 1) [16,64] r4118 c4118
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u314
  · exact u315

def b4119 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 132, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 13 98 134 296 19 48 65 192 448), lower := (rows 13 98 134 296 19 48 65 128 256), losses := [] }

theorem u4119 : Upper (D 7) (R 7) [12,96,130,288,3,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4119 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r4120 : Route 9 := (fun mask => (mask,id))

def c4120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4120 : Upper (D 7) (R 7) [12,96,130,288,3,16,128] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,3,16,128] 13 (by decide) (choices 1) [1,64] r4120 c4120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u316
  · exact u317

def r4121 : Route 9 := (fun mask => (mask,id))

def c4121 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4121 : Upper (D 7) (R 7) [12,96,130,288,3,128,1] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,3,128,1] 13 (by decide) (choices 1) [16,64] r4121 c4121
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u318
  · exact u319

def r4122 : Route 9 := (fun mask => (mask,id))

def c4122 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u4122 : Upper (D 7) (R 7) [12,96,130,288,3,128,16] 13 := by
  apply FastRouting.sound _ _ [12,96,130,288,3,128,16] 13 (by decide) (choices 1) [1,64] r4122 c4122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u320
  · exact u321

def b4123 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 4, region := 424, targets := 66 }], pairs := [(1,7),(3,1),(3,6),(4,7)], upper := (rows 13 98 134 296 81 33 66 144 400), lower := (rows 13 98 134 296 81 33 66 128 256), losses := [] }

theorem u4123 : Upper (D 7) (R 7) [12,96,130,288,65,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4123 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4124 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 134 296 81 33 80 130 386), lower := (rows 13 98 134 296 81 33 80 128 256), losses := [] }

theorem u4124 : Upper (D 7) (R 7) [12,96,130,288,65,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4124 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4125 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 298, targets := 128 }], pairs := [(1,7),(3,7),(4,1),(4,5)], upper := (rows 13 98 134 296 81 33 192 146 274), lower := (rows 13 98 134 296 81 33 192 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 49 196 128 256), good := (rows 125 96 196 296 113 49 192 192 256) },{ target := 5, region := (rows 1 2 4 8 17 0 196 128 256), good := (rows 93 66 198 264 81 17 192 192 256) }] }

theorem u4125 : Upper (D 7) (R 7) [12,96,130,288,65,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4125 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4126 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 80, targets := 162 },{ cop := 4, region := 162, targets := 1 }], pairs := [(1,0),(4,1),(4,5),(4,7)], upper := (rows 13 98 134 296 81 160 65 146 274), lower := (rows 13 98 134 296 81 160 65 128 256), losses := [] }

theorem u4126 : Upper (D 7) (R 7) [12,96,130,288,65,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4126 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4127 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 4, region := 424, targets := 66 }], pairs := [(1,0),(1,7),(3,1),(3,6)], upper := (rows 13 98 134 296 81 160 66 145 273), lower := (rows 13 98 134 296 81 160 66 128 256), losses := [] }

theorem u4127 : Upper (D 7) (R 7) [12,96,130,288,65,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4127 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4128 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 80, targets := 162 }], pairs := [(4,1),(4,5),(4,7)], upper := (rows 13 98 134 296 81 160 80 131 259), lower := (rows 13 98 134 296 81 160 80 128 256), losses := [] }

theorem u4128 : Upper (D 7) (R 7) [12,96,130,288,65,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4128 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4129 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 4, region := 362, targets := 128 }], pairs := [(1,0),(1,7),(2,5),(3,7)], upper := (rows 13 98 134 296 145 33 66 208 336), lower := (rows 13 98 134 296 145 33 66 128 256), losses := [{ target := 5, region := (rows 1 2 70 8 49 0 70 131 259), good := (rows 477 470 454 280 401 401 454 128 256) }] }

theorem u4129 : Upper (D 7) (R 7) [12,96,130,288,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4129 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4130 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 396, targets := 1 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7),(2,0),(3,0)], upper := (rows 13 98 134 296 145 33 80 194 322), lower := (rows 13 98 134 296 145 33 80 128 256), losses := [] }

theorem u4130 : Upper (D 7) (R 7) [12,96,130,288,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4130 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4131 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 396, targets := 1 },{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7),(2,0),(3,0)], upper := (rows 13 98 134 296 145 48 65 194 322), lower := (rows 13 98 134 296 145 48 65 128 256), losses := [] }

theorem u4131 : Upper (D 7) (R 7) [12,96,130,288,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4131 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4132 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 66, targets := 129 },{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(1,7),(2,0)], upper := (rows 13 98 134 296 145 48 66 193 321), lower := (rows 13 98 134 296 145 48 66 128 256), losses := [] }

theorem u4132 : Upper (D 7) (R 7) [12,96,130,288,129,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4132 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4133 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 412, targets := 1 },{ cop := 1, region := 148, targets := 32 }], pairs := [(2,0),(2,5),(3,0),(4,0)], upper := (rows 13 98 134 296 208 33 65 146 274), lower := (rows 13 98 134 296 208 33 65 128 256), losses := [] }

theorem u4133 : Upper (D 7) (R 7) [12,96,130,288,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4133 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4134 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 80, targets := 33 },{ cop := 3, region := 66, targets := 129 }], pairs := [(1,0),(1,7),(4,0),(4,5)], upper := (rows 13 98 134 296 208 33 66 145 273), lower := (rows 13 98 134 296 208 33 66 128 256), losses := [] }

theorem u4134 : Upper (D 7) (R 7) [12,96,130,288,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4134 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4135 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 397, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 13 98 134 296 208 33 80 131 259), lower := (rows 13 98 134 296 208 33 80 128 256), losses := [] }

theorem u4135 : Upper (D 7) (R 7) [12,96,130,288,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4135 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4136 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 114, targets := 128 },{ cop := 1, region := 132, targets := 1 }], pairs := [(1,7),(2,0),(4,7)], upper := (rows 13 98 134 392 19 33 80 224 352), lower := (rows 13 98 134 392 19 33 80 128 256), losses := [] }

theorem u4136 : Upper (D 7) (R 7) [12,96,130,384,3,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4136 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4137 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 413, targets := 32 }], pairs := [(0,5),(2,5),(3,5),(4,5)], upper := (rows 13 98 134 392 19 33 96 208 336), lower := (rows 13 98 134 392 19 33 96 128 256), losses := [] }

theorem u4137 : Upper (D 7) (R 7) [12,96,130,384,3,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4137 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4138 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 85, targets := 34 }], pairs := [(0,1),(0,5),(2,1)], upper := (rows 13 98 148 168 81 288 65 130 258), lower := (rows 13 98 148 168 81 288 65 128 256), losses := [] }

theorem u4138 : Upper (D 7) (R 7) [12,96,144,160,65,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4138 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4139 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 370, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(1,0),(1,7),(4,7)], upper := (rows 13 98 148 168 81 288 66 131 259), lower := (rows 13 98 148 168 81 288 66 128 256), losses := [] }

theorem u4139 : Upper (D 7) (R 7) [12,96,144,160,65,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4139 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u4139
end Delivery.IrregularNine14.P07

import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4080 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 290 76 137 176 48 101 165 293), lower := (rows 67 290 76 137 176 48 64 128 256), losses := [] }

theorem u4080 : Upper (D 8) (R 8) [66,288,72,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4080 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4081 : PairBound 9 := { available := 52, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 67 290 76 168 145 33 116 180 308), lower := (rows 67 290 76 168 145 33 64 128 256), losses := [] }

theorem u4081 : Upper (D 8) (R 8) [66,288,72,160,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4082 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 290 76 168 145 36 113 177 305), lower := (rows 67 290 76 168 145 36 64 128 256), losses := [] }

theorem u4082 : Upper (D 8) (R 8) [66,288,72,160,129,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4082 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4083 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 290 76 168 145 48 101 165 293), lower := (rows 67 290 76 168 145 48 64 128 256), losses := [] }

theorem u4083 : Upper (D 8) (R 8) [66,288,72,160,129,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4083 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4084 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 290 100 137 148 33 120 184 312), lower := (rows 67 290 100 137 148 33 64 128 256), losses := [] }

theorem u4084 : Upper (D 8) (R 8) [66,288,96,129,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4084 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4085 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 290 100 137 148 40 113 177 305), lower := (rows 67 290 100 137 148 40 64 128 256), losses := [] }

theorem u4085 : Upper (D 8) (R 8) [66,288,96,129,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4085 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4086 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 290 100 137 148 48 105 169 297), lower := (rows 67 290 100 137 148 48 64 128 256), losses := [] }

theorem u4086 : Upper (D 8) (R 8) [66,288,96,129,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4086 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4087 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 290 100 137 176 33 92 156 284), lower := (rows 67 290 100 137 176 33 64 128 256), losses := [] }

theorem u4087 : Upper (D 8) (R 8) [66,288,96,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4088 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 290 100 137 176 36 89 153 281), lower := (rows 67 290 100 137 176 36 64 128 256), losses := [] }

theorem u4088 : Upper (D 8) (R 8) [66,288,96,129,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4088 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4089 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 67 290 100 137 176 40 85 149 277), lower := (rows 67 290 100 137 176 40 64 128 256), losses := [] }

theorem u4089 : Upper (D 8) (R 8) [66,288,96,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4089 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4090 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 67 290 100 137 176 48 77 141 269), lower := (rows 67 290 100 137 176 48 64 128 256), losses := [] }

theorem u4090 : Upper (D 8) (R 8) [66,288,96,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4090 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4091 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 290 100 140 176 33 89 153 281), lower := (rows 67 290 100 140 176 33 64 128 256), losses := [] }

theorem u4091 : Upper (D 8) (R 8) [66,288,96,132,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4091 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4092 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 67 290 100 140 176 40 81 145 273), lower := (rows 67 290 100 140 176 40 64 128 256), losses := [] }

theorem u4092 : Upper (D 8) (R 8) [66,288,96,132,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4092 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4093 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 67 290 100 140 176 48 73 137 265), lower := (rows 67 290 100 140 176 48 64 128 256), losses := [] }

theorem u4093 : Upper (D 8) (R 8) [66,288,96,132,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4093 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4094 : PairBound 9 := { available := 176, camps := [{ cop := 5, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 67 386 13 44 112 33 240 176 432), lower := (rows 67 386 13 44 112 33 64 128 256), losses := [] }

theorem u4094 : Upper (D 8) (R 8) [66,384,9,36,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4094 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4095 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 386 13 44 112 48 225 161 417), lower := (rows 67 386 13 44 112 48 64 128 256), losses := [] }

theorem u4095 : Upper (D 8) (R 8) [66,384,9,36,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4095 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4096 : PairBound 9 := { available := 49, camps := [], pairs := [(4,0)], upper := (rows 67 386 13 44 112 160 113 177 305), lower := (rows 67 386 13 44 112 160 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 162 64 128 256), good := (rows 114 418 28 44 112 160 64 160 256) }] }

theorem u4096 : Upper (D 8) (R 8) [66,384,9,36,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4096 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4097 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 386 13 44 176 33 112 240 368), lower := (rows 67 386 13 44 176 33 64 128 256), losses := [] }

theorem u4097 : Upper (D 8) (R 8) [66,384,9,36,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4097 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4098 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 386 13 44 176 48 97 225 353), lower := (rows 67 386 13 44 176 48 64 128 256), losses := [] }

theorem u4098 : Upper (D 8) (R 8) [66,384,9,36,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4098 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4099 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 44, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 13 44 176 96 113 177 305), lower := (rows 67 386 13 44 176 96 64 128 256), losses := [] }

theorem u4099 : Upper (D 8) (R 8) [66,384,9,36,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4099 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4100 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 44, targets := 64 }], pairs := [(2,6)], upper := (rows 67 386 13 44 208 33 112 176 304), lower := (rows 67 386 13 44 208 33 64 128 256), losses := [] }

theorem u4100 : Upper (D 8) (R 8) [66,384,9,36,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4101 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 386 13 44 208 48 97 161 289), lower := (rows 67 386 13 44 208 48 64 128 256), losses := [] }

theorem u4101 : Upper (D 8) (R 8) [66,384,9,36,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4101 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4102 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 60, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 28 41 112 33 228 164 420), lower := (rows 67 386 28 41 112 33 64 128 256), losses := [] }

theorem u4102 : Upper (D 8) (R 8) [66,384,24,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4102 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4103 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 386 28 41 112 36 225 161 417), lower := (rows 67 386 28 41 112 36 64 128 256), losses := [] }

theorem u4103 : Upper (D 8) (R 8) [66,384,24,33,96,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4103 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4104 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 84, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 28 41 112 160 101 165 293), lower := (rows 67 386 28 41 112 160 64 128 256), losses := [] }

theorem u4104 : Upper (D 8) (R 8) [66,384,24,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4105 : PairBound 9 := { available := 100, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 28 41 176 33 100 228 356), lower := (rows 67 386 28 41 176 33 64 128 256), losses := [] }

theorem u4105 : Upper (D 8) (R 8) [66,384,24,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4106 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 386 28 41 176 36 97 225 353), lower := (rows 67 386 28 41 176 36 64 128 256), losses := [] }

theorem u4106 : Upper (D 8) (R 8) [66,384,24,33,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4106 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4107 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 406, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 28 41 176 96 101 165 293), lower := (rows 67 386 28 41 176 96 64 128 256), losses := [] }

theorem u4107 : Upper (D 8) (R 8) [66,384,24,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4108 : PairBound 9 := { available := 36, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 28 41 208 33 100 164 292), lower := (rows 67 386 28 41 208 33 64 128 256), losses := [] }

theorem u4108 : Upper (D 8) (R 8) [66,384,24,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4109 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 386 28 41 208 36 97 161 289), lower := (rows 67 386 28 41 208 36 64 128 256), losses := [] }

theorem u4109 : Upper (D 8) (R 8) [66,384,24,33,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4109 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4110 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 40, targets := 128 }], pairs := [(3,7)], upper := (rows 67 386 28 104 176 33 101 165 293), lower := (rows 67 386 28 104 176 33 64 128 256), losses := [] }

theorem u4110 : Upper (D 8) (R 8) [66,384,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4111 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 386 28 104 176 36 97 161 289), lower := (rows 67 386 28 104 176 36 64 128 256), losses := [] }

theorem u4111 : Upper (D 8) (R 8) [66,384,24,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4111 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4112 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 36, targets := 128 }], pairs := [(2,7)], upper := (rows 67 386 37 56 84 33 232 168 424), lower := (rows 67 386 37 56 84 33 64 128 256), losses := [] }

theorem u4112 : Upper (D 8) (R 8) [66,384,33,48,68,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4112 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4113 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 67 386 37 56 84 40 225 161 417), lower := (rows 67 386 37 56 84 40 64 128 256), losses := [] }

theorem u4113 : Upper (D 8) (R 8) [66,384,33,48,68,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4113 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4114 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 88, targets := 128 }], pairs := [(3,7)], upper := (rows 67 386 37 56 84 160 105 169 297), lower := (rows 67 386 37 56 84 160 64 128 256), losses := [] }

theorem u4114 : Upper (D 8) (R 8) [66,384,33,48,68,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4114 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4115 : PairBound 9 := { available := 104, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 37 56 148 33 104 232 360), lower := (rows 67 386 37 56 148 33 64 128 256), losses := [] }

theorem u4115 : Upper (D 8) (R 8) [66,384,33,48,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4115 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4116 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 67 386 37 56 148 40 97 225 353), lower := (rows 67 386 37 56 148 40 64 128 256), losses := [] }

theorem u4116 : Upper (D 8) (R 8) [66,384,33,48,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4116 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4117 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 410, targets := 64 }], pairs := [(1,6)], upper := (rows 67 386 37 56 148 96 105 169 297), lower := (rows 67 386 37 56 148 96 64 128 256), losses := [] }

theorem u4117 : Upper (D 8) (R 8) [66,384,33,48,132,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4117 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4118 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 37 56 208 33 108 172 300), lower := (rows 67 386 37 56 208 33 64 128 256), losses := [] }

theorem u4118 : Upper (D 8) (R 8) [66,384,33,48,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4119 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 386 37 56 208 36 105 169 297), lower := (rows 67 386 37 56 208 36 64 128 256), losses := [] }

theorem u4119 : Upper (D 8) (R 8) [66,384,33,48,192,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4119 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4120 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 386 37 56 208 40 101 165 293), lower := (rows 67 386 37 56 208 40 64 128 256), losses := [] }

theorem u4120 : Upper (D 8) (R 8) [66,384,33,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4120 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4121 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 37 76 152 33 112 176 304), lower := (rows 67 386 37 76 152 33 64 128 256), losses := [] }

theorem u4121 : Upper (D 8) (R 8) [66,384,33,68,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4122 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 386 37 76 152 48 97 161 289), lower := (rows 67 386 37 76 152 48 64 128 256), losses := [] }

theorem u4122 : Upper (D 8) (R 8) [66,384,33,68,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4122 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4123 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 37 76 176 33 120 184 312), lower := (rows 67 386 37 76 176 33 64 128 256), losses := [] }

theorem u4123 : Upper (D 8) (R 8) [66,384,33,68,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4124 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 386 37 76 176 40 113 177 305), lower := (rows 67 386 37 76 176 40 64 128 256), losses := [] }

theorem u4124 : Upper (D 8) (R 8) [66,384,33,68,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4124 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4125 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 386 37 76 176 48 105 169 297), lower := (rows 67 386 37 76 176 48 64 128 256), losses := [] }

theorem u4125 : Upper (D 8) (R 8) [66,384,33,68,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4125 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4126 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 37 88 148 33 104 168 296), lower := (rows 67 386 37 88 148 33 64 128 256), losses := [] }

theorem u4126 : Upper (D 8) (R 8) [66,384,33,80,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4126 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4127 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 67 386 37 88 148 40 97 161 289), lower := (rows 67 386 37 88 148 40 64 128 256), losses := [] }

theorem u4127 : Upper (D 8) (R 8) [66,384,33,80,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4127 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4128 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 37 88 176 33 108 172 300), lower := (rows 67 386 37 88 176 33 64 128 256), losses := [] }

theorem u4128 : Upper (D 8) (R 8) [66,384,33,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4129 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 386 37 88 176 36 105 169 297), lower := (rows 67 386 37 88 176 36 64 128 256), losses := [] }

theorem u4129 : Upper (D 8) (R 8) [66,384,33,80,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4129 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4130 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 386 37 88 176 40 101 165 293), lower := (rows 67 386 37 88 176 40 64 128 256), losses := [] }

theorem u4130 : Upper (D 8) (R 8) [66,384,33,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4130 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4131 : PairBound 9 := { available := 56, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 37 104 148 33 120 184 312), lower := (rows 67 386 37 104 148 33 64 128 256), losses := [] }

theorem u4131 : Upper (D 8) (R 8) [66,384,33,96,132,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4132 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 386 37 104 148 40 113 177 305), lower := (rows 67 386 37 104 148 40 64 128 256), losses := [] }

theorem u4132 : Upper (D 8) (R 8) [66,384,33,96,132,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4132 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4133 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 67 386 37 104 148 48 105 169 297), lower := (rows 67 386 37 104 148 48 64 128 256), losses := [] }

theorem u4133 : Upper (D 8) (R 8) [66,384,33,96,132,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4133 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4134 : PairBound 9 := { available := 52, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 37 104 152 33 116 180 308), lower := (rows 67 386 37 104 152 33 64 128 256), losses := [] }

theorem u4134 : Upper (D 8) (R 8) [66,384,33,96,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4134 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4135 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 67 386 37 104 152 36 113 177 305), lower := (rows 67 386 37 104 152 36 64 128 256), losses := [] }

theorem u4135 : Upper (D 8) (R 8) [66,384,33,96,136,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4135 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4136 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 67 386 37 104 152 48 101 165 293), lower := (rows 67 386 37 104 152 48 64 128 256), losses := [] }

theorem u4136 : Upper (D 8) (R 8) [66,384,33,96,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4136 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4137 : PairBound 9 := { available := 28, camps := [{ cop := 2, region := 474, targets := 1 }], pairs := [(1,0)], upper := (rows 67 386 37 104 176 33 92 156 284), lower := (rows 67 386 37 104 176 33 64 128 256), losses := [] }

theorem u4137 : Upper (D 8) (R 8) [66,384,33,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4138 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 67 386 37 104 176 36 89 153 281), lower := (rows 67 386 37 104 176 36 64 128 256), losses := [] }

theorem u4138 : Upper (D 8) (R 8) [66,384,33,96,160,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4138 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4139 : PairBound 9 := { available := 21, camps := [], pairs := [], upper := (rows 67 386 37 104 176 40 85 149 277), lower := (rows 67 386 37 104 176 40 64 128 256), losses := [] }

theorem u4139 : Upper (D 8) (R 8) [66,384,33,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4139 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u4139
end Delivery.IrregularNine14.P08

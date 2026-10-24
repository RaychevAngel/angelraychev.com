import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b0 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 7 74 164 296 336 33 192 144 288), lower := (rows 7 74 164 296 336 33 192 144 256), losses := [] }

theorem u0 : Upper (D 10) (R 10) [6,72,160,288,320,1,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b0 [(5,0),(7,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 199, targets := 256 }], pairs := [(0,8)], upper := (rows 7 74 164 296 336 33 192 160 272), lower := (rows 7 74 164 296 336 33 192 160 256), losses := [] }

theorem u1 : Upper (D 10) (R 10) [6,72,160,288,320,1,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 35 70 164 200 273 48 320 136 288), lower := (rows 35 70 164 200 273 48 320 136 256), losses := [] }

theorem u2 : Upper (D 10) (R 10) [34,68,160,192,257,16,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2 [(5,4),(7,3)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 8, camps := [{ cop := 0, region := 132, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 164 200 273 48 320 160 264), lower := (rows 35 70 164 200 273 48 320 160 256), losses := [] }

theorem u3 : Upper (D 10) (R 10) [34,68,160,192,257,16,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 194 76 152 273 288 96 132 288), lower := (rows 35 194 76 152 273 288 96 132 256), losses := [] }

theorem u4 : Upper (D 10) (R 10) [34,192,72,144,257,256,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b4 [(7,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 195, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 35 194 76 152 273 288 96 160 260), lower := (rows 35 194 76 152 273 288 96 160 256), losses := [] }

theorem u5 : Upper (D 10) (R 10) [34,192,72,144,257,256,32,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b5 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 32, camps := [], pairs := [], upper := (rows 35 194 76 392 273 48 96 132 288), lower := (rows 35 194 76 392 273 48 96 132 256), losses := [] }

theorem u6 : Upper (D 10) (R 10) [34,192,72,384,257,16,32,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b6 [(5,4),(7,2)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 4, camps := [{ cop := 1, region := 268, targets := 32 }], pairs := [(2,5)], upper := (rows 35 194 76 392 273 48 96 160 260), lower := (rows 35 194 76 392 273 48 96 160 256), losses := [] }

theorem u7 : Upper (D 10) (R 10) [34,192,72,384,257,16,32,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b7 [(5,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 75, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 11 52 104 208 288 96 384 384), lower := (rows 7 11 52 104 208 288 96 128 256), losses := [] }

theorem u8 : Upper (D 10) (R 10) [6,9,48,96,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b8 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 11 52 104 208 288 192 416 288), lower := (rows 7 11 52 104 208 288 192 128 256), losses := [] }

theorem u9 : Upper (D 10) (R 10) [6,9,48,96,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b9 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 151, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 52 104 208 288 320 160 416), lower := (rows 7 11 52 104 208 288 320 128 256), losses := [] }

theorem u10 : Upper (D 10) (R 10) [6,9,48,96,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b10 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 79, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 11 84 104 176 288 96 384 384), lower := (rows 7 11 84 104 176 288 96 128 256), losses := [] }

theorem u11 : Upper (D 10) (R 10) [6,9,80,96,160,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b11 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 84 104 176 288 192 416 288), lower := (rows 7 11 84 104 176 288 192 128 256), losses := [] }

theorem u12 : Upper (D 10) (R 10) [6,9,80,96,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b12 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 151, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 11 84 104 176 288 320 160 416), lower := (rows 7 11 84 104 176 288 320 128 256), losses := [] }

theorem u13 : Upper (D 10) (R 10) [6,9,80,96,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b13 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 37 104 176 288 192 448 320), lower := (rows 7 26 37 104 176 288 192 128 256), losses := [] }

theorem u14 : Upper (D 10) (R 10) [6,24,33,96,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b14 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 151, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 37 104 176 288 320 192 448), lower := (rows 7 26 37 104 176 288 320 128 256), losses := [] }

theorem u15 : Upper (D 10) (R 10) [6,24,33,96,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b15 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 100 41 176 288 192 448 320), lower := (rows 7 26 100 41 176 288 192 128 256), losses := [] }

theorem u16 : Upper (D 10) (R 10) [6,24,96,33,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b16 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 100 41 176 288 320 192 448), lower := (rows 7 26 100 41 176 288 320 128 256), losses := [] }

theorem u17 : Upper (D 10) (R 10) [6,24,96,33,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b17 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 68, targets := 384 }], pairs := [(2,7),(2,8)], upper := (rows 7 26 100 41 208 288 96 384 384), lower := (rows 7 26 100 41 208 288 96 128 256), losses := [] }

theorem u18 : Upper (D 10) (R 10) [6,24,96,33,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b18 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 26 100 41 208 288 192 416 288), lower := (rows 7 26 100 41 208 288 192 128 256), losses := [] }

theorem u19 : Upper (D 10) (R 10) [6,24,96,33,192,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b19 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 100 41 208 288 320 160 416), lower := (rows 7 26 100 41 208 288 320 128 256), losses := [] }

theorem u20 : Upper (D 10) (R 10) [6,24,96,33,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b20 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 272, targets := 128 }], pairs := [(4,7)], upper := (rows 7 26 100 168 304 33 192 448 320), lower := (rows 7 26 100 168 304 33 192 128 256), losses := [] }

theorem u21 : Upper (D 10) (R 10) [6,24,96,160,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b21 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 82, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 7 26 196 41 112 288 96 384 384), lower := (rows 7 26 196 41 112 288 96 128 256), losses := [] }

theorem u22 : Upper (D 10) (R 10) [6,24,192,33,96,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b22 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 26 196 41 112 288 192 416 288), lower := (rows 7 26 196 41 112 288 192 128 256), losses := [] }

theorem u23 : Upper (D 10) (R 10) [6,24,192,33,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b23 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 143, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 26 196 41 112 288 320 160 416), lower := (rows 7 26 196 41 112 288 320 128 256), losses := [] }

theorem u24 : Upper (D 10) (R 10) [6,24,192,33,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b24 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 87, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 168 112 288 80 384 384), lower := (rows 7 35 76 168 112 288 80 128 256), losses := [] }

theorem u25 : Upper (D 10) (R 10) [6,33,72,160,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b25 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 71, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 76 168 112 288 192 400 272), lower := (rows 7 35 76 168 112 288 192 128 256), losses := [] }

theorem u26 : Upper (D 10) (R 10) [6,33,72,160,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b26 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 144, camps := [{ cop := 4, region := 143, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 76 168 112 288 320 144 400), lower := (rows 7 35 76 168 112 288 320 128 256), losses := [] }

theorem u27 : Upper (D 10) (R 10) [6,33,72,160,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b27 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 87, targets := 256 }], pairs := [(0,8)], upper := (rows 7 35 76 168 208 288 80 416 288), lower := (rows 7 35 76 168 208 288 80 128 256), losses := [] }

theorem u28 : Upper (D 10) (R 10) [6,33,72,160,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b28 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 272, camps := [{ cop := 3, region := 71, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 35 76 168 208 288 96 400 272), lower := (rows 7 35 76 168 208 288 96 128 256), losses := [] }

theorem u29 : Upper (D 10) (R 10) [6,33,72,160,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b29 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 296, targets := 64 }], pairs := [(2,5),(3,6)], upper := (rows 7 35 76 168 208 288 320 176 304), lower := (rows 7 35 76 168 208 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 12 8 24 0 352 128 256), good := (rows 7 67 92 220 208 320 320 128 320) }] }

theorem u30 : Upper (D 10) (R 10) [6,33,72,160,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b30 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 168 336 288 80 160 416), lower := (rows 7 35 76 168 336 288 80 128 256), losses := [] }

theorem u31 : Upper (D 10) (R 10) [6,33,72,160,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b31 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 168 336 288 96 144 400), lower := (rows 7 35 76 168 336 288 96 128 256), losses := [] }

theorem u32 : Upper (D 10) (R 10) [6,33,72,160,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b32 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 76 168 336 288 192 176 304), lower := (rows 7 35 76 168 336 288 192 128 256), losses := [] }

theorem u33 : Upper (D 10) (R 10) [6,33,72,160,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b33 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 168 400 288 80 224 352), lower := (rows 7 35 76 168 400 288 80 128 256), losses := [] }

theorem u34 : Upper (D 10) (R 10) [6,33,72,160,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b34 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 71, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 35 76 168 400 288 96 208 336), lower := (rows 7 35 76 168 400 288 96 128 256), losses := [] }

theorem u35 : Upper (D 10) (R 10) [6,33,72,160,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b35 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 135, targets := 256 }], pairs := [(0,8)], upper := (rows 7 35 196 104 280 288 80 160 416), lower := (rows 7 35 196 104 280 288 80 128 256), losses := [] }

theorem u36 : Upper (D 10) (R 10) [6,33,192,96,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b36 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 72, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 35 196 104 280 288 96 144 400), lower := (rows 7 35 196 104 280 288 96 128 256), losses := [] }

theorem u37 : Upper (D 10) (R 10) [6,33,192,96,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b37 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 35 196 104 280 288 192 176 304), lower := (rows 7 35 196 104 280 288 192 128 256), losses := [] }

theorem u38 : Upper (D 10) (R 10) [6,33,192,96,264,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b38 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 392, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 52 200 336 33 96 384 384), lower := (rows 7 42 52 200 336 33 96 128 256), losses := [] }

theorem u39 : Upper (D 10) (R 10) [6,40,48,192,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b39 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 52 200 336 33 192 416 288), lower := (rows 7 42 52 200 336 33 192 128 256), losses := [] }

theorem u40 : Upper (D 10) (R 10) [6,40,48,192,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b40 [(5,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 84 200 176 288 65 416 288), lower := (rows 7 42 84 200 176 288 65 128 256), losses := [] }

theorem u41 : Upper (D 10) (R 10) [6,40,80,192,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b41 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 84 200 176 288 96 385 257), lower := (rows 7 42 84 200 176 288 96 128 256), losses := [] }

theorem u42 : Upper (D 10) (R 10) [6,40,80,192,160,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b42 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(2,5),(4,6)], upper := (rows 7 42 84 200 176 288 320 161 289), lower := (rows 7 42 84 200 176 288 320 128 256), losses := [{ target := 5, region := (rows 1 2 20 24 16 0 352 128 256), good := (rows 7 74 92 200 220 320 320 128 320) }] }

theorem u43 : Upper (D 10) (R 10) [6,40,80,192,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b43 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 290, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 84 200 400 288 65 160 288), lower := (rows 7 42 84 200 400 288 65 128 256), losses := [] }

theorem u44 : Upper (D 10) (R 10) [6,40,80,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b44 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 64 },{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7),(4,6)], upper := (rows 7 42 84 200 400 288 96 161 289), lower := (rows 7 42 84 200 400 288 96 128 256), losses := [] }

theorem u45 : Upper (D 10) (R 10) [6,40,80,192,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b45 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 84 392 176 96 65 416 288), lower := (rows 7 42 84 392 176 96 65 128 256), losses := [] }

theorem u46 : Upper (D 10) (R 10) [6,40,80,384,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b46 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 84 392 176 96 96 385 257), lower := (rows 7 42 84 392 176 96 96 128 256), losses := [] }

theorem u47 : Upper (D 10) (R 10) [6,40,80,384,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b47 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7),(4,8)], upper := (rows 7 42 84 392 176 96 320 161 289), lower := (rows 7 42 84 392 176 96 320 128 256), losses := [{ target := 8, region := (rows 1 2 4 8 17 100 64 129 0), good := (rows 183 42 116 136 176 96 96 128 0) }] }

theorem u48 : Upper (D 10) (R 10) [6,40,80,384,160,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b48 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 88 176 288 65 384 384), lower := (rows 7 42 100 88 176 288 65 128 256), losses := [] }

theorem u49 : Upper (D 10) (R 10) [6,40,96,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b49 [(6,0)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 100 88 176 288 192 385 257), lower := (rows 7 42 100 88 176 288 192 128 256), losses := [] }

theorem u50 : Upper (D 10) (R 10) [6,40,96,80,160,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b50 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 100 88 176 288 320 129 385), lower := (rows 7 42 100 88 176 288 320 128 256), losses := [] }

theorem u51 : Upper (D 10) (R 10) [6,40,96,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b51 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 320, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8)], upper := (rows 7 42 100 137 176 288 80 448 320), lower := (rows 7 42 100 137 176 288 80 128 256), losses := [] }

theorem u52 : Upper (D 10) (R 10) [6,40,96,129,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b52 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 100 137 176 288 320 208 336), lower := (rows 7 42 100 137 176 288 320 128 256), losses := [] }

theorem u53 : Upper (D 10) (R 10) [6,40,96,129,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b53 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 137 208 288 80 416 288), lower := (rows 7 42 100 137 208 288 80 128 256), losses := [] }

theorem u54 : Upper (D 10) (R 10) [6,40,96,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b54 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 272, camps := [{ cop := 1, region := 69, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 137 208 288 96 400 272), lower := (rows 7 42 100 137 208 288 96 128 256), losses := [] }

theorem u55 : Upper (D 10) (R 10) [6,40,96,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b55 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 155, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 42 100 137 208 288 320 176 304), lower := (rows 7 42 100 137 208 288 320 128 256), losses := [] }

theorem u56 : Upper (D 10) (R 10) [6,40,96,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b56 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 137 336 288 80 160 416), lower := (rows 7 42 100 137 336 288 80 128 256), losses := [] }

theorem u57 : Upper (D 10) (R 10) [6,40,96,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b57 [(6,4)]
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 69, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 42 100 137 336 288 96 144 400), lower := (rows 7 42 100 137 336 288 96 128 256), losses := [] }

theorem u58 : Upper (D 10) (R 10) [6,40,96,129,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b58 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 308, targets := 128 }], pairs := [(2,7),(4,7)], upper := (rows 7 42 100 137 336 288 192 176 304), lower := (rows 7 42 100 137 336 288 192 128 256), losses := [] }

theorem u59 : Upper (D 10) (R 10) [6,40,96,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b59 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P10

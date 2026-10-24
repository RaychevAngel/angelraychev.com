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

def b0 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 266, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 392 176 96 65 129 288), lower := (rows 7 42 84 392 176 96 65 129 256), losses := [] }

theorem u0 : Upper (D 8) (R 8) [6,40,80,384,160,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b0 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 144, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 84 392 176 96 65 160 257), lower := (rows 7 42 84 392 176 96 65 160 256), losses := [] }

theorem u1 : Upper (D 8) (R 8) [6,40,80,384,160,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 280, targets := 1 }], pairs := [(3,0)], upper := (rows 7 74 164 56 400 96 65 129 288), lower := (rows 7 74 164 56 400 96 65 129 256), losses := [] }

theorem u2 : Upper (D 8) (R 8) [6,72,160,48,384,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b2 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 74 164 56 400 96 65 160 257), lower := (rows 7 74 164 56 400 96 65 160 256), losses := [] }

theorem u3 : Upper (D 8) (R 8) [6,72,160,48,384,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b3 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 344, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 14 56 336 160 96 129 288), lower := (rows 193 7 14 56 336 160 96 129 256), losses := [] }

theorem u4 : Upper (D 8) (R 8) [192,5,10,48,320,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b4 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 272, targets := 32 }], pairs := [(4,5)], upper := (rows 193 7 14 56 336 160 96 160 257), lower := (rows 193 7 14 56 336 160 96 160 256), losses := [] }

theorem u5 : Upper (D 8) (R 8) [192,5,10,48,320,128,32,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b5 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 104 336 160 65 160 416), lower := (rows 7 11 52 104 336 160 65 128 256), losses := [] }

theorem u6 : Upper (D 8) (R 8) [6,9,48,96,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b6 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 75, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 104 336 160 96 129 385), lower := (rows 7 11 52 104 336 160 96 128 256), losses := [] }

theorem u7 : Upper (D 8) (R 8) [6,9,48,96,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 52 104 336 160 192 161 289), lower := (rows 7 11 52 104 336 160 192 128 256), losses := [] }

theorem u8 : Upper (D 8) (R 8) [6,9,48,96,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b8 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 32, camps := [{ cop := 6, region := 436, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 52 200 336 160 65 160 288), lower := (rows 7 11 52 200 336 160 65 128 256), losses := [] }

theorem u9 : Upper (D 8) (R 8) [6,9,48,192,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b9 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 52 200 336 160 96 161 289), lower := (rows 7 11 52 200 336 160 96 128 256), losses := [] }

theorem u10 : Upper (D 8) (R 8) [6,9,48,192,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b10 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 404, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 168 304 96 65 160 416), lower := (rows 7 11 84 168 304 96 65 128 256), losses := [] }

theorem u11 : Upper (D 8) (R 8) [6,9,80,160,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b11 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 168 304 96 96 129 385), lower := (rows 7 11 84 168 304 96 96 128 256), losses := [] }

theorem u12 : Upper (D 8) (R 8) [6,9,80,160,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b12 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 84 168 304 96 192 161 289), lower := (rows 7 11 84 168 304 96 192 128 256), losses := [] }

theorem u13 : Upper (D 8) (R 8) [6,9,80,160,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b13 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 404, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 168 400 96 65 160 288), lower := (rows 7 11 84 168 400 96 65 128 256), losses := [] }

theorem u14 : Upper (D 8) (R 8) [6,9,80,160,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b14 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 168 400 96 96 161 289), lower := (rows 7 11 84 168 400 96 96 128 256), losses := [] }

theorem u15 : Upper (D 8) (R 8) [6,9,80,160,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b15 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 148, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 296 176 96 65 160 416), lower := (rows 7 11 84 296 176 96 65 128 256), losses := [] }

theorem u16 : Upper (D 8) (R 8) [6,9,80,288,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b16 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 296 176 96 96 129 385), lower := (rows 7 11 84 296 176 96 96 128 256), losses := [] }

theorem u17 : Upper (D 8) (R 8) [6,9,80,288,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b17 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 84 296 176 96 192 161 289), lower := (rows 7 11 84 296 176 96 192 128 256), losses := [] }

theorem u18 : Upper (D 8) (R 8) [6,9,80,288,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b18 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 148, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 392 176 96 65 160 288), lower := (rows 7 11 84 392 176 96 65 128 256), losses := [] }

theorem u19 : Upper (D 8) (R 8) [6,9,80,384,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b19 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 116, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 84 392 176 96 96 161 289), lower := (rows 7 11 84 392 176 96 96 128 256), losses := [] }

theorem u20 : Upper (D 8) (R 8) [6,9,80,384,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b20 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 56 336 160 65 160 416), lower := (rows 7 11 100 56 336 160 65 128 256), losses := [] }

theorem u21 : Upper (D 8) (R 8) [6,9,96,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 56 336 160 96 129 385), lower := (rows 7 11 100 56 336 160 96 128 256), losses := [] }

theorem u22 : Upper (D 8) (R 8) [6,9,96,48,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 100 56 336 160 192 161 289), lower := (rows 7 11 100 56 336 160 192 128 256), losses := [] }

theorem u23 : Upper (D 8) (R 8) [6,9,96,48,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b23 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 304 160 65 224 352), lower := (rows 7 11 100 152 304 160 65 128 256), losses := [] }

theorem u24 : Upper (D 8) (R 8) [6,9,96,144,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b24 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 304 160 96 193 321), lower := (rows 7 11 100 152 304 160 96 128 256), losses := [] }

theorem u25 : Upper (D 8) (R 8) [6,9,96,144,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b25 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 32, camps := [{ cop := 6, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 336 160 65 160 288), lower := (rows 7 11 100 152 336 160 65 128 256), losses := [] }

theorem u26 : Upper (D 8) (R 8) [6,9,96,144,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b26 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 100 152 336 160 96 161 289), lower := (rows 7 11 100 152 336 160 96 128 256), losses := [] }

theorem u27 : Upper (D 8) (R 8) [6,9,96,144,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b27 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 32, camps := [{ cop := 6, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 56 336 160 65 160 288), lower := (rows 7 11 196 56 336 160 65 128 256), losses := [] }

theorem u28 : Upper (D 8) (R 8) [6,9,192,48,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b28 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 196 56 336 160 96 161 289), lower := (rows 7 11 196 56 336 160 96 128 256), losses := [] }

theorem u29 : Upper (D 8) (R 8) [6,9,192,48,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b29 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 388, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 292 88 176 96 65 160 416), lower := (rows 7 11 292 88 176 96 65 128 256), losses := [] }

theorem u30 : Upper (D 8) (R 8) [6,9,288,80,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b30 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 292 88 176 96 96 129 385), lower := (rows 7 11 292 88 176 96 96 128 256), losses := [] }

theorem u31 : Upper (D 8) (R 8) [6,9,288,80,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b31 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 7 11 292 88 176 96 192 161 289), lower := (rows 7 11 292 88 176 96 192 128 256), losses := [] }

theorem u32 : Upper (D 8) (R 8) [6,9,288,80,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b32 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 32, camps := [{ cop := 6, region := 420, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 324 152 112 160 65 160 288), lower := (rows 7 11 324 152 112 160 65 128 256), losses := [] }

theorem u33 : Upper (D 8) (R 8) [6,9,320,144,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b33 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 88, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 324 152 112 160 96 161 289), lower := (rows 7 11 324 152 112 160 96 128 256), losses := [] }

theorem u34 : Upper (D 8) (R 8) [6,9,320,144,96,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b34 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 37 104 304 160 65 192 448), lower := (rows 7 26 37 104 304 160 65 128 256), losses := [] }

theorem u35 : Upper (D 8) (R 8) [6,24,33,96,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b35 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 37 104 304 160 192 193 321), lower := (rows 7 26 37 104 304 160 192 128 256), losses := [] }

theorem u36 : Upper (D 8) (R 8) [6,24,33,96,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b36 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 69 168 304 96 65 160 416), lower := (rows 7 26 69 168 304 96 65 128 256), losses := [] }

theorem u37 : Upper (D 8) (R 8) [6,24,65,160,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b37 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 69 168 304 96 96 129 385), lower := (rows 7 26 69 168 304 96 96 128 256), losses := [] }

theorem u38 : Upper (D 8) (R 8) [6,24,65,160,288,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b38 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 304, targets := 128 }], pairs := [(4,7)], upper := (rows 7 26 69 168 304 96 192 161 289), lower := (rows 7 26 69 168 304 96 192 128 256), losses := [] }

theorem u39 : Upper (D 8) (R 8) [6,24,65,160,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b39 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 41 304 160 65 192 448), lower := (rows 7 26 100 41 304 160 65 128 256), losses := [] }

theorem u40 : Upper (D 8) (R 8) [6,24,96,33,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b40 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 100 41 304 160 192 193 321), lower := (rows 7 26 100 41 304 160 192 128 256), losses := [] }

theorem u41 : Upper (D 8) (R 8) [6,24,96,33,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b41 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 96, camps := [{ cop := 6, region := 164, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 137 304 160 65 224 352), lower := (rows 7 26 100 137 304 160 65 128 256), losses := [] }

theorem u42 : Upper (D 8) (R 8) [6,24,96,129,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b42 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 137 304 160 96 193 321), lower := (rows 7 26 100 137 304 160 96 128 256), losses := [] }

theorem u43 : Upper (D 8) (R 8) [6,24,96,129,288,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b43 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 410, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 100 168 304 33 65 192 448), lower := (rows 7 26 100 168 304 33 65 128 256), losses := [] }

theorem u44 : Upper (D 8) (R 8) [6,24,96,160,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b44 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 100 168 304 33 192 193 321), lower := (rows 7 26 100 168 304 33 192 128 256), losses := [] }

theorem u45 : Upper (D 8) (R 8) [6,24,96,160,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b45 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 91, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 292 41 112 160 65 192 448), lower := (rows 7 26 292 41 112 160 65 128 256), losses := [] }

theorem u46 : Upper (D 8) (R 8) [6,24,288,33,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b46 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 26 292 41 112 160 192 193 321), lower := (rows 7 26 292 41 112 160 192 128 256), losses := [] }

theorem u47 : Upper (D 8) (R 8) [6,24,288,33,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b47 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 388, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 292 73 176 96 65 160 416), lower := (rows 7 26 292 73 176 96 65 128 256), losses := [] }

theorem u48 : Upper (D 8) (R 8) [6,24,288,65,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b48 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 26 292 73 176 96 96 129 385), lower := (rows 7 26 292 73 176 96 96 128 256), losses := [] }

theorem u49 : Upper (D 8) (R 8) [6,24,288,65,160,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b49 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 292, targets := 128 }], pairs := [(2,7)], upper := (rows 7 26 292 73 176 96 192 161 289), lower := (rows 7 26 292 73 176 96 192 128 256), losses := [] }

theorem u50 : Upper (D 8) (R 8) [6,24,288,65,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b50 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 146, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 292 104 176 33 65 192 448), lower := (rows 7 26 292 104 176 33 65 128 256), losses := [] }

theorem u51 : Upper (D 8) (R 8) [6,24,288,96,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b51 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 74, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 292 104 176 33 192 193 321), lower := (rows 7 26 292 104 176 33 192 128 256), losses := [] }

theorem u52 : Upper (D 8) (R 8) [6,24,288,96,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b52 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 296 112 160 65 144 400), lower := (rows 7 35 76 296 112 160 65 128 256), losses := [] }

theorem u53 : Upper (D 8) (R 8) [6,33,72,288,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b53 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 35 76 296 112 160 80 129 385), lower := (rows 7 35 76 296 112 160 80 128 256), losses := [] }

theorem u54 : Upper (D 8) (R 8) [6,33,72,288,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b54 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 296 112 160 192 145 273), lower := (rows 7 35 76 296 112 160 192 128 256), losses := [] }

theorem u55 : Upper (D 8) (R 8) [6,33,72,288,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b55 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 296 208 160 65 176 304), lower := (rows 7 35 76 296 208 160 65 128 256), losses := [] }

theorem u56 : Upper (D 8) (R 8) [6,33,72,288,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b56 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 35 76 296 208 160 80 161 289), lower := (rows 7 35 76 296 208 160 80 128 256), losses := [] }

theorem u57 : Upper (D 8) (R 8) [6,33,72,288,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b57 [(6,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 296 208 160 96 145 273), lower := (rows 7 35 76 296 208 160 96 128 256), losses := [] }

theorem u58 : Upper (D 8) (R 8) [6,33,72,288,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b58 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 48, camps := [{ cop := 6, region := 444, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 324 104 152 160 65 176 304), lower := (rows 7 35 324 104 152 160 65 128 256), losses := [] }

theorem u59 : Upper (D 8) (R 8) [6,33,320,96,136,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b59 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P08

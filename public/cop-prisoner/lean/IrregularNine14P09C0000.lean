import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b0 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 5, region := 336, targets := 32 },{ cop := 5, region := 328, targets := 128 },{ cop := 6, region := 176, targets := 64 }], pairs := [(3,0),(3,7),(4,0),(4,5),(4,6)], upper := (rows 7 11 21 104 400 160 320 160 320), lower := (rows 7 11 21 104 400 160 320 160 256), losses := [] }

theorem u0 : Upper (D 9) (R 9) [6,9,17,96,384,128,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b0 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 5, region := 272, targets := 64 },{ cop := 5, region := 328, targets := 128 },{ cop := 6, region := 144, targets := 32 }], pairs := [(3,0),(3,7),(4,0),(4,5),(4,6)], upper := (rows 7 11 21 104 400 160 320 192 288), lower := (rows 7 11 21 104 400 160 320 192 256), losses := [] }

theorem u1 : Upper (D 9) (R 9) [6,9,17,96,384,128,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 348, targets := 1 },{ cop := 5, region := 340, targets := 128 }], pairs := [(2,0),(2,7),(3,0),(4,0),(4,7)], upper := (rows 7 11 100 152 304 160 320 129 320), lower := (rows 7 11 100 152 304 160 320 129 256), losses := [] }

theorem u2 : Upper (D 9) (R 9) [6,9,96,144,288,128,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 188, targets := 1 },{ cop := 4, region := 200, targets := 32 },{ cop := 4, region := 68, targets := 128 }], pairs := [(2,0),(2,7),(3,0),(3,5),(4,0)], upper := (rows 7 11 100 152 304 160 320 192 257), lower := (rows 7 11 100 152 304 160 320 192 256), losses := [] }

theorem u3 : Upper (D 9) (R 9) [6,9,96,144,288,128,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b3 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 327, targets := 128 },{ cop := 5, region := 324, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 7 11 100 168 400 33 320 144 320), lower := (rows 7 11 100 168 400 33 320 144 256), losses := [] }

theorem u4 : Upper (D 9) (R 9) [6,9,96,160,384,1,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b4 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 16, camps := [{ cop := 6, region := 175, targets := 256 },{ cop := 5, region := 468, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 11 100 168 400 33 320 192 272), lower := (rows 7 11 100 168 400 33 320 192 256), losses := [] }

theorem u5 : Upper (D 9) (R 9) [6,9,96,160,384,1,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b5 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 340, targets := 129 },{ cop := 0, region := 136, targets := 64 }], pairs := [(2,0),(2,7),(3,6),(4,0),(4,7)], upper := (rows 7 26 100 137 304 160 320 129 320), lower := (rows 7 26 100 137 304 160 320 129 256), losses := [] }

theorem u6 : Upper (D 9) (R 9) [6,24,96,129,288,128,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 306, targets := 64 },{ cop := 6, region := 180, targets := 1 },{ cop := 0, region := 456, targets := 32 }], pairs := [(1,6),(2,0),(3,5),(4,0),(4,6)], upper := (rows 7 26 100 137 304 160 320 192 257), lower := (rows 7 26 100 137 304 160 320 192 256), losses := [] }

theorem u7 : Upper (D 9) (R 9) [6,24,96,129,288,128,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b7 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 342, targets := 1 },{ cop := 0, region := 168, targets := 320 }], pairs := [(1,0),(2,0),(3,6),(3,8),(4,0)], upper := (rows 7 26 100 168 400 33 320 129 320), lower := (rows 7 26 100 168 400 33 320 129 256), losses := [] }

theorem u8 : Upper (D 9) (R 9) [6,24,96,160,384,1,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 357, targets := 128 },{ cop := 2, region := 136, targets := 257 },{ cop := 6, region := 144, targets := 1 }], pairs := [(0,7),(2,7),(3,0),(3,8),(4,0)], upper := (rows 7 26 100 168 400 33 320 192 257), lower := (rows 7 26 100 168 400 33 320 192 256), losses := [] }

theorem u9 : Upper (D 9) (R 9) [6,24,96,160,384,1,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 2, region := 400, targets := 32 }], pairs := [(0,6),(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 35 76 137 208 288 96 384 272), lower := (rows 7 35 76 137 208 288 96 384 256), losses := [{ target := 5, region := (rows 1 2 4 11 84 0 64 511 341), good := (rows 415 395 476 393 464 384 464 384 384) },{ target := 6, region := (rows 5 10 4 10 16 432 0 432 272), good := (rows 15 171 15 171 432 416 160 416 416) }] }

theorem u10 : Upper (D 9) (R 9) [6,33,72,129,192,256,32,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b10 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 136, targets := 320 },{ cop := 3, region := 340, targets := 1 }], pairs := [(2,0),(3,6),(3,8),(4,0)], upper := (rows 7 35 76 137 400 48 320 160 320), lower := (rows 7 35 76 137 400 48 320 160 256), losses := [] }

theorem u11 : Upper (D 9) (R 9) [6,33,72,129,384,16,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b11 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 372, targets := 1 },{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(2,0),(4,0),(4,6)], upper := (rows 7 35 76 137 400 48 320 192 288), lower := (rows 7 35 76 137 400 48 320 192 256), losses := [] }

theorem u12 : Upper (D 9) (R 9) [6,33,72,129,384,16,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b12 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 3, region := 356, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(2,7)], upper := (rows 7 35 76 137 400 288 96 144 320), lower := (rows 7 35 76 137 400 288 96 144 256), losses := [] }

theorem u13 : Upper (D 9) (R 9) [6,33,72,129,384,256,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b13 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 207, targets := 256 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,8)], upper := (rows 7 35 76 137 400 288 96 192 272), lower := (rows 7 35 76 137 400 288 96 192 256), losses := [] }

theorem u14 : Upper (D 9) (R 9) [6,33,72,129,384,256,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b14 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 307, targets := 64 },{ cop := 6, region := 444, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 35 196 88 400 288 65 136 288), lower := (rows 7 35 196 88 400 288 65 136 256), losses := [] }

theorem u15 : Upper (D 9) (R 9) [6,33,192,80,384,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b15 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 6, region := 444, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,0)], upper := (rows 7 35 196 88 400 288 65 160 264), lower := (rows 7 35 196 88 400 288 65 160 256), losses := [] }

theorem u16 : Upper (D 9) (R 9) [6,33,192,80,384,256,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b16 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 7, region := 380, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,0)], upper := (rows 7 35 196 88 400 288 96 129 264), lower := (rows 7 35 196 88 400 288 96 129 256), losses := [] }

theorem u17 : Upper (D 9) (R 9) [6,33,192,80,384,256,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b17 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 64 },{ cop := 3, region := 132, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 7 35 196 88 400 288 96 136 257), lower := (rows 7 35 196 88 400 288 96 136 256), losses := [] }

theorem u18 : Upper (D 9) (R 9) [6,33,192,80,384,256,32,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b18 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 180, targets := 1 },{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 392, targets := 64 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(2,0),(3,5),(3,6),(4,0)], upper := (rows 7 42 84 137 176 96 320 384 257), lower := (rows 7 42 84 137 176 96 320 384 256), losses := [] }

theorem u19 : Upper (D 9) (R 9) [6,40,80,129,160,64,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b19 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 136, targets := 352 },{ cop := 3, region := 374, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(3,6),(3,8)], upper := (rows 7 42 84 137 400 288 96 129 320), lower := (rows 7 42 84 137 400 288 96 129 256), losses := [] }

theorem u20 : Upper (D 9) (R 9) [6,40,80,129,384,256,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b20 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 306, targets := 64 },{ cop := 5, region := 212, targets := 1 },{ cop := 3, region := 272, targets := 32 }], pairs := [(1,6),(2,0),(4,0),(4,5),(4,6)], upper := (rows 7 42 84 137 400 288 96 192 257), lower := (rows 7 42 84 137 400 288 96 192 256), losses := [] }

theorem u21 : Upper (D 9) (R 9) [6,40,80,129,384,256,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b21 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 310, targets := 1 },{ cop := 0, region := 200, targets := 288 }], pairs := [(1,0),(2,0),(3,5),(3,8),(4,0)], upper := (rows 7 42 84 200 400 288 65 129 288), lower := (rows 7 42 84 200 400 288 65 129 256), losses := [] }

theorem u22 : Upper (D 9) (R 9) [6,40,80,192,384,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b22 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 144, targets := 65 }], pairs := [(0,5),(1,0),(3,0),(4,0),(4,6)], upper := (rows 7 42 84 200 400 288 65 160 257), lower := (rows 7 42 84 200 400 288 65 160 256), losses := [{ target := 0, region := (rows 0 6 4 12 304 304 64 438 256), good := (rows 142 186 254 200 432 432 64 176 432) },{ target := 5, region := (rows 3 2 14 8 24 0 67 128 323), good := (rows 327 351 340 476 400 256 321 128 256) }] }

theorem u23 : Upper (D 9) (R 9) [6,40,80,192,384,256,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b23 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 453, targets := 32 },{ cop := 7, region := 48, targets := 65 }], pairs := [(0,5),(1,0),(2,5),(4,0),(4,6)], upper := (rows 7 42 196 88 304 160 65 384 257), lower := (rows 7 42 196 88 304 160 65 384 256), losses := [{ target := 0, region := (rows 0 15 12 12 400 444 64 400 256), good := (rows 46 46 254 254 432 176 66 432 432) }] }

theorem u24 : Upper (D 9) (R 9) [6,40,192,80,288,128,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b24 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 272, targets := 193 },{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(4,0),(4,6),(4,7)], upper := (rows 7 42 196 328 304 160 65 129 272), lower := (rows 7 42 196 328 304 160 65 129 256), losses := [] }

theorem u25 : Upper (D 9) (R 9) [6,40,192,320,288,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b25 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 182, targets := 1 },{ cop := 0, region := 328, targets := 32 }], pairs := [(1,0),(2,0),(3,5),(4,0)], upper := (rows 7 42 196 328 304 160 65 144 257), lower := (rows 7 42 196 328 304 160 65 144 256), losses := [] }

theorem u26 : Upper (D 9) (R 9) [6,40,192,320,288,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b26 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 280, targets := 33 },{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 196 328 400 33 96 129 272), lower := (rows 7 42 196 328 400 33 96 129 256), losses := [] }

theorem u27 : Upper (D 9) (R 9) [6,40,192,320,384,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b27 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 148, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 7 42 196 328 400 33 96 144 257), lower := (rows 7 42 196 328 400 33 96 144 256), losses := [] }

theorem u28 : Upper (D 9) (R 9) [6,40,192,320,384,1,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b28 [(7,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 184, targets := 320 }], pairs := [(3,6),(3,8),(4,6),(4,8)], upper := (rows 7 98 388 25 176 40 320 129 320), lower := (rows 7 98 388 25 176 40 320 129 256), losses := [] }

theorem u29 : Upper (D 9) (R 9) [6,96,384,17,160,8,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b29 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 144, targets := 257 },{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,8)], upper := (rows 7 98 388 25 176 40 320 192 257), lower := (rows 7 98 388 25 176 40 320 192 256), losses := [] }

theorem u30 : Upper (D 9) (R 9) [6,96,384,17,160,8,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b30 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 8, camps := [{ cop := 4, region := 302, targets := 1 },{ cop := 0, region := 208, targets := 288 }], pairs := [(1,0),(2,0),(3,0),(4,5),(4,8)], upper := (rows 7 98 388 56 208 288 65 129 264), lower := (rows 7 98 388 56 208 288 65 129 256), losses := [] }

theorem u31 : Upper (D 9) (R 9) [6,96,384,48,192,256,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b31 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 152, targets := 257 }], pairs := [(3,0),(3,8),(4,0),(4,8)], upper := (rows 7 98 388 56 208 288 65 136 257), lower := (rows 7 98 388 56 208 288 65 136 256), losses := [] }

theorem u32 : Upper (D 9) (R 9) [6,96,384,48,192,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b32 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 128, camps := [{ cop := 4, region := 236, targets := 1 },{ cop := 0, region := 464, targets := 32 },{ cop := 7, region := 296, targets := 64 }], pairs := [(2,0),(3,0),(3,6),(4,5)], upper := (rows 35 7 76 168 273 288 80 192 384), lower := (rows 35 7 76 168 273 288 80 192 256), losses := [] }

theorem u33 : Upper (D 9) (R 9) [34,5,72,160,257,256,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b33 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 307, targets := 64 },{ cop := 6, region := 444, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 7 196 88 400 288 65 136 288), lower := (rows 35 7 196 88 400 288 65 136 256), losses := [] }

theorem u34 : Upper (D 9) (R 9) [34,5,192,80,384,256,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b34 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 6, region := 444, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,0)], upper := (rows 35 7 196 88 400 288 65 160 264), lower := (rows 35 7 196 88 400 288 65 160 256), losses := [] }

theorem u35 : Upper (D 9) (R 9) [34,5,192,80,384,256,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b35 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 8, camps := [{ cop := 5, region := 199, targets := 256 },{ cop := 7, region := 380, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(2,8),(3,0)], upper := (rows 35 7 196 88 400 288 96 129 264), lower := (rows 35 7 196 88 400 288 96 129 256), losses := [] }

theorem u36 : Upper (D 9) (R 9) [34,5,192,80,384,256,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b36 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 307, targets := 64 },{ cop := 3, region := 132, targets := 1 }], pairs := [(0,6),(1,6),(2,0),(4,6)], upper := (rows 35 7 196 88 400 288 96 136 257), lower := (rows 35 7 196 88 400 288 96 136 256), losses := [] }

theorem u37 : Upper (D 9) (R 9) [34,5,192,80,384,256,32,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b37 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 216, targets := 1 },{ cop := 0, region := 452, targets := 32 },{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(2,5),(3,0),(4,0)], upper := (rows 35 14 69 152 112 288 192 384 257), lower := (rows 35 14 69 152 112 288 192 384 256), losses := [] }

theorem u38 : Upper (D 9) (R 9) [34,12,65,144,96,256,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b38 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 196, targets := 288 },{ cop := 2, region := 304, targets := 129 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(2,5),(2,8),(4,0),(4,7)], upper := (rows 35 14 69 152 336 288 192 129 288), lower := (rows 35 14 69 152 336 288 192 129 256), losses := [] }

theorem u39 : Upper (D 9) (R 9) [34,12,65,144,320,256,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b39 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 216, targets := 1 },{ cop := 0, region := 196, targets := 256 },{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(2,8),(3,0),(4,0)], upper := (rows 35 14 69 152 336 288 192 160 257), lower := (rows 35 14 69 152 336 288 192 160 256), losses := [] }

theorem u40 : Upper (D 9) (R 9) [34,12,65,144,320,256,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b40 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 152, targets := 320 },{ cop := 4, region := 366, targets := 1 }], pairs := [(1,0),(3,6),(3,8),(4,6),(4,8)], upper := (rows 35 14 84 168 145 288 320 129 320), lower := (rows 35 14 84 168 145 288 320 129 256), losses := [] }

theorem u41 : Upper (D 9) (R 9) [34,12,80,160,129,256,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b41 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 },{ cop := 4, region := 296, targets := 64 }], pairs := [(0,6),(0,7),(2,5),(3,6),(4,5)], upper := (rows 35 14 84 168 145 288 320 192 257), lower := (rows 35 14 84 168 145 288 320 192 256), losses := [] }

theorem u42 : Upper (D 9) (R 9) [34,12,80,160,129,256,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b42 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 339, targets := 128 },{ cop := 3, region := 372, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(4,7)], upper := (rows 35 67 28 137 304 160 320 132 320), lower := (rows 35 67 28 137 304 160 320 132 256), losses := [] }

theorem u43 : Upper (D 9) (R 9) [34,65,24,129,288,128,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b43 [(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 4, camps := [{ cop := 6, region := 171, targets := 256 },{ cop := 3, region := 308, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,0)], upper := (rows 35 67 28 137 304 160 320 192 260), lower := (rows 35 67 28 137 304 160 320 192 256), losses := [] }

theorem u44 : Upper (D 9) (R 9) [34,65,24,129,288,128,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b44 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 203, targets := 256 },{ cop := 6, region := 316, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,0),(3,8)], upper := (rows 35 67 28 168 336 288 192 129 260), lower := (rows 35 67 28 168 336 288 192 129 256), losses := [] }

theorem u45 : Upper (D 9) (R 9) [34,65,24,160,320,256,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b45 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 220, targets := 1 },{ cop := 6, region := 291, targets := 128 }], pairs := [(0,7),(2,0),(3,0),(4,0)], upper := (rows 35 67 28 168 336 288 192 132 257), lower := (rows 35 67 28 168 336 288 192 132 256), losses := [] }

theorem u46 : Upper (D 9) (R 9) [34,65,24,160,320,256,128,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b46 [(7,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 346, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 133 268 400 40 80 160 320), lower := (rows 35 67 133 268 400 40 80 160 256), losses := [] }

theorem u47 : Upper (D 9) (R 9) [34,65,129,260,384,8,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b47 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 132, targets := 288 },{ cop := 2, region := 296, targets := 1 }], pairs := [(2,5),(2,8),(3,0)], upper := (rows 35 67 133 268 400 40 80 192 288), lower := (rows 35 67 133 268 400 40 80 192 256), losses := [] }

theorem u48 : Upper (D 9) (R 9) [34,65,129,260,384,8,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b48 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 346, targets := 32 }], pairs := [(1,5),(3,5),(4,5)], upper := (rows 35 67 133 268 400 48 72 160 320), lower := (rows 35 67 133 268 400 48 72 160 256), losses := [] }

theorem u49 : Upper (D 9) (R 9) [34,65,129,260,384,16,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b49 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 132, targets := 288 },{ cop := 2, region := 312, targets := 1 }], pairs := [(2,5),(2,8),(3,0)], upper := (rows 35 67 133 268 400 48 72 192 288), lower := (rows 35 67 133 268 400 48 72 192 256), losses := [] }

theorem u50 : Upper (D 9) (R 9) [34,65,129,260,384,16,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b50 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 184, targets := 1 },{ cop := 0, region := 336, targets := 128 },{ cop := 1, region := 417, targets := 64 },{ cop := 2, region := 322, targets := 32 }], pairs := [(0,6),(1,5),(3,0),(4,0),(4,7)], upper := (rows 35 70 13 152 112 160 320 384 257), lower := (rows 35 70 13 152 112 160 320 384 256), losses := [] }

theorem u51 : Upper (D 9) (R 9) [34,68,9,144,96,128,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b51 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 161, targets := 320 },{ cop := 2, region := 322, targets := 129 },{ cop := 5, region := 344, targets := 1 }], pairs := [(0,6),(0,8),(1,0),(1,7),(3,0)], upper := (rows 35 70 13 152 304 160 320 129 320), lower := (rows 35 70 13 152 304 160 320 129 256), losses := [] }

theorem u52 : Upper (D 9) (R 9) [34,68,9,144,288,128,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b52 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 1, camps := [{ cop := 6, region := 184, targets := 1 },{ cop := 0, region := 272, targets := 64 },{ cop := 0, region := 272, targets := 128 },{ cop := 1, region := 161, targets := 256 }], pairs := [(0,8),(3,0),(4,0),(4,6),(4,7)], upper := (rows 35 70 13 152 304 160 320 192 257), lower := (rows 35 70 13 152 304 160 320 192 256), losses := [] }

theorem u53 : Upper (D 9) (R 9) [34,68,9,144,288,128,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b53 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 374, targets := 1 },{ cop := 7, region := 8, targets := 96 }], pairs := [(1,0),(2,0),(3,5),(3,6),(4,0)], upper := (rows 35 70 28 137 400 288 96 129 320), lower := (rows 35 70 28 137 400 288 96 129 256), losses := [] }

theorem u54 : Upper (D 9) (R 9) [34,68,24,129,384,256,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b54 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 355, targets := 128 },{ cop := 3, region := 276, targets := 32 },{ cop := 3, region := 276, targets := 64 }], pairs := [(0,7),(1,7),(2,5),(2,6),(4,5)], upper := (rows 35 70 28 137 400 288 96 192 257), lower := (rows 35 70 28 137 400 288 96 192 256), losses := [] }

theorem u55 : Upper (D 9) (R 9) [34,68,24,129,384,256,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b55 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 370, targets := 1 },{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7),(1,0),(1,7),(4,0)], upper := (rows 35 70 133 25 208 288 320 136 288), lower := (rows 35 70 133 25 208 288 320 136 256), losses := [] }

theorem u56 : Upper (D 9) (R 9) [34,68,129,17,192,256,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b56 [(7,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 346, targets := 32 },{ cop := 0, region := 132, targets := 320 }], pairs := [(1,5),(2,6),(2,8),(3,5),(4,5)], upper := (rows 35 70 133 25 208 288 320 160 264), lower := (rows 35 70 133 25 208 288 320 160 256), losses := [] }

theorem u57 : Upper (D 9) (R 9) [34,68,129,17,192,256,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b57 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 346, targets := 32 },{ cop := 0, region := 132, targets := 64 }], pairs := [(1,5),(2,6),(3,5),(4,5)], upper := (rows 35 70 133 25 400 40 320 160 320), lower := (rows 35 70 133 25 400 40 320 160 256), losses := [] }

theorem u58 : Upper (D 9) (R 9) [34,68,129,17,384,8,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b58 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 32, camps := [{ cop := 2, region := 312, targets := 64 },{ cop := 6, region := 144, targets := 33 }], pairs := [(3,6),(4,0),(4,5),(4,6)], upper := (rows 35 70 133 25 400 40 320 192 288), lower := (rows 35 70 133 25 400 40 320 192 256), losses := [] }

theorem u59 : Upper (D 9) (R 9) [34,68,129,17,384,8,256,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b59 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P09

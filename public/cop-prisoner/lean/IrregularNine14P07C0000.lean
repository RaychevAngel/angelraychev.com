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

def b0 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 11 37 328 208 160 96 130 272), lower := (rows 7 11 37 328 208 160 96 130 256), losses := [] }

theorem u0 : Upper (D 7) (R 7) [6,9,33,320,192,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b0 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 11 37 328 208 160 96 144 258), lower := (rows 7 11 37 328 208 160 96 144 256), losses := [] }

theorem u1 : Upper (D 7) (R 7) [6,9,33,320,192,128,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b2 : PairBound 9 := { available := 128, camps := [{ cop := 3, region := 272, targets := 35 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 11 52 200 336 33 96 130 384), lower := (rows 7 11 52 200 336 33 96 130 256), losses := [{ target := 0, region := (rows 0 2 100 41 125 32 100 131 427), good := (rows 478 410 380 476 340 508 380 386 256) }] }

theorem u2 : Upper (D 7) (R 7) [6,9,48,192,320,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b2 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b3 : PairBound 9 := { available := 128, camps := [{ cop := 3, region := 272, targets := 35 }], pairs := [(2,0),(4,0),(4,1),(4,5)], upper := (rows 7 11 52 200 336 34 96 129 384), lower := (rows 7 11 52 200 336 34 96 129 256), losses := [{ target := 0, region := (rows 0 2 167 136 154 35 231 128 392), good := (rows 118 382 116 476 336 118 100 508 256) }] }

theorem u3 : Upper (D 7) (R 7) [6,9,48,192,320,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b3 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b4 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 72, targets := 3 }], pairs := [(2,0),(3,0),(3,1),(4,0)], upper := (rows 7 11 52 200 336 160 96 129 258), lower := (rows 7 11 52 200 336 160 96 129 256), losses := [{ target := 0, region := (rows 0 2 174 168 147 168 238 128 259), good := (rows 342 382 124 252 336 252 108 508 256) }] }

theorem u4 : Upper (D 7) (R 7) [6,9,48,192,320,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b4 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b5 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 72, targets := 3 }], pairs := [(2,1),(3,0),(3,1),(4,1)], upper := (rows 7 11 52 200 336 160 96 130 257), lower := (rows 7 11 52 200 336 160 96 130 256), losses := [{ target := 1, region := (rows 1 0 174 168 147 168 238 128 259), good := (rows 341 381 124 252 336 252 108 508 256) }] }

theorem u5 : Upper (D 7) (R 7) [6,9,48,192,320,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b5 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b6 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 52 328 145 96 192 130 288), lower := (rows 7 11 52 328 145 96 192 130 256), losses := [] }

theorem u6 : Upper (D 7) (R 7) [6,9,48,320,129,64,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b6 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b7 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 330, targets := 32 }], pairs := [(1,5),(2,1),(3,5),(4,1)], upper := (rows 7 11 52 328 145 96 192 160 258), lower := (rows 7 11 52 328 145 96 192 160 256), losses := [] }

theorem u7 : Upper (D 7) (R 7) [6,9,48,320,129,64,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b7 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b8 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0),(3,1)], upper := (rows 7 11 52 328 146 96 192 129 288), lower := (rows 7 11 52 328 146 96 192 129 256), losses := [] }

theorem u8 : Upper (D 7) (R 7) [6,9,48,320,130,64,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b8 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b9 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 244, targets := 1 },{ cop := 8, region := 232, targets := 3 }], pairs := [(2,0),(3,0),(3,1),(4,0)], upper := (rows 7 11 52 328 146 96 192 160 257), lower := (rows 7 11 52 328 146 96 192 160 256), losses := [] }

theorem u9 : Upper (D 7) (R 7) [6,9,48,320,130,64,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b9 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b10 : PairBound 9 := { available := 128, camps := [{ cop := 4, region := 264, targets := 35 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 7 11 52 328 208 33 96 130 384), lower := (rows 7 11 52 328 208 33 96 130 256), losses := [{ target := 0, region := (rows 0 2 100 125 49 32 100 131 435), good := (rows 478 410 380 332 476 508 380 386 256) }] }

theorem u10 : Upper (D 7) (R 7) [6,9,48,320,192,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b10 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b11 : PairBound 9 := { available := 128, camps := [{ cop := 4, region := 264, targets := 35 }], pairs := [(2,0),(3,0),(3,1),(3,5)], upper := (rows 7 11 52 328 208 34 96 129 384), lower := (rows 7 11 52 328 208 34 96 129 256), losses := [{ target := 0, region := (rows 0 2 132 156 144 35 231 128 400), good := (rows 110 106 380 328 476 98 96 508 256) }] }

theorem u11 : Upper (D 7) (R 7) [6,9,48,320,192,2,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b11 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b12 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 272, targets := 131 },{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5),(4,0),(4,1),(4,7)], upper := (rows 7 26 100 137 304 160 65 130 320), lower := (rows 7 26 100 137 304 160 65 130 256), losses := [] }

theorem u12 : Upper (D 7) (R 7) [6,24,96,129,288,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b12 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b13 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 26 100 137 304 160 65 192 258), lower := (rows 7 26 100 137 304 160 65 192 256), losses := [] }

theorem u13 : Upper (D 7) (R 7) [6,24,96,129,288,128,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b13 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b14 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 272, targets := 131 },{ cop := 0, region := 136, targets := 2 }], pairs := [(3,1),(4,0),(4,1),(4,7)], upper := (rows 7 26 100 137 304 160 66 129 320), lower := (rows 7 26 100 137 304 160 66 129 256), losses := [] }

theorem u14 : Upper (D 7) (R 7) [6,24,96,129,288,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b14 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b15 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 306, targets := 64 },{ cop := 6, region := 164, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(4,6)], upper := (rows 7 26 100 137 304 160 66 192 257), lower := (rows 7 26 100 137 304 160 66 192 256), losses := [] }

theorem u15 : Upper (D 7) (R 7) [6,24,96,129,288,128,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b15 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b16 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0),(4,1)], upper := (rows 7 35 13 328 208 160 96 130 272), lower := (rows 7 35 13 328 208 160 96 130 256), losses := [] }

theorem u16 : Upper (D 7) (R 7) [6,33,9,320,192,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b16 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b17 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 335, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 13 328 208 160 96 144 258), lower := (rows 7 35 13 328 208 160 96 144 256), losses := [] }

theorem u17 : Upper (D 7) (R 7) [6,33,9,320,192,128,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b17 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b18 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 344, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 69 152 304 160 72 130 320), lower := (rows 7 35 69 152 304 160 72 130 256), losses := [] }

theorem u18 : Upper (D 7) (R 7) [6,33,65,144,288,128,8,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b18 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b19 : PairBound 9 := { available := 2, camps := [{ cop := 8, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 69 152 304 160 72 192 258), lower := (rows 7 35 69 152 304 160 72 192 256), losses := [] }

theorem u19 : Upper (D 7) (R 7) [6,33,65,144,288,128,8,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b19 [(6,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b20 : PairBound 9 := { available := 32, camps := [{ cop := 6, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 69 152 336 40 192 130 288), lower := (rows 7 35 69 152 336 40 192 130 256), losses := [] }

theorem u20 : Upper (D 7) (R 7) [6,33,65,144,320,8,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b20 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b21 : PairBound 9 := { available := 2, camps := [{ cop := 8, region := 248, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 69 152 336 40 192 160 258), lower := (rows 7 35 69 152 336 40 192 160 256), losses := [] }

theorem u21 : Upper (D 7) (R 7) [6,33,65,144,320,8,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b21 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b22 : PairBound 9 := { available := 64, camps := [{ cop := 0, region := 152, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 35 76 137 146 288 96 144 320), lower := (rows 7 35 76 137 146 288 96 144 256), losses := [] }

theorem u22 : Upper (D 7) (R 7) [6,33,72,129,130,256,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b22 [(5,8),(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b23 : PairBound 9 := { available := 16, camps := [{ cop := 1, region := 204, targets := 2 },{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 7 35 76 137 146 288 96 192 272), lower := (rows 7 35 76 137 146 288 96 192 256), losses := [] }

theorem u23 : Upper (D 7) (R 7) [6,33,72,129,130,256,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b23 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b24 : PairBound 9 := { available := 16, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 76 137 208 288 96 130 272), lower := (rows 7 35 76 137 208 288 96 130 256), losses := [] }

theorem u24 : Upper (D 7) (R 7) [6,33,72,129,192,256,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b24 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b25 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 220, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 137 208 288 96 144 258), lower := (rows 7 35 76 137 208 288 96 144 256), losses := [] }

theorem u25 : Upper (D 7) (R 7) [6,33,72,129,192,256,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b25 [(5,8),(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b26 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 76 137 400 48 96 130 320), lower := (rows 7 35 76 137 400 48 96 130 256), losses := [] }

theorem u26 : Upper (D 7) (R 7) [6,33,72,129,384,16,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b26 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b27 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 204, targets := 2 },{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(2,1),(3,1)], upper := (rows 7 35 76 137 400 48 96 192 258), lower := (rows 7 35 76 137 400 48 96 192 256), losses := [] }

theorem u27 : Upper (D 7) (R 7) [6,33,72,129,384,16,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b27 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b28 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 1, region := 336, targets := 2 },{ cop := 1, region := 336, targets := 128 }], pairs := [(0,6),(1,6),(4,1),(4,7)], upper := (rows 7 35 76 152 304 160 65 130 320), lower := (rows 7 35 76 152 304 160 65 130 256), losses := [] }

theorem u28 : Upper (D 7) (R 7) [6,33,72,144,288,128,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b28 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b29 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 272, targets := 65 },{ cop := 1, region := 272, targets := 128 }], pairs := [(2,0),(4,0),(4,6),(4,7)], upper := (rows 7 35 76 152 304 160 65 192 258), lower := (rows 7 35 76 152 304 160 65 192 256), losses := [{ target := 0, region := (rows 0 2 196 205 83 237 64 196 259), good := (rows 446 314 252 188 304 172 508 252 256) }] }

theorem u29 : Upper (D 7) (R 7) [6,33,72,144,288,128,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b29 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b30 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 336, targets := 129 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,7)], upper := (rows 7 35 76 152 304 160 66 129 320), lower := (rows 7 35 76 152 304 160 66 129 256), losses := [] }

theorem u30 : Upper (D 7) (R 7) [6,33,72,144,288,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b30 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b31 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 272, targets := 2 },{ cop := 1, region := 272, targets := 64 },{ cop := 1, region := 272, targets := 128 }], pairs := [(2,1),(4,1),(4,6),(4,7)], upper := (rows 7 35 76 152 304 160 66 192 257), lower := (rows 7 35 76 152 304 160 66 192 256), losses := [{ target := 1, region := (rows 1 0 196 205 83 237 64 196 259), good := (rows 445 313 252 188 304 172 508 252 256) }] }

theorem u31 : Upper (D 7) (R 7) [6,33,72,144,288,128,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b31 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b32 : PairBound 9 := { available := 16, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 5, region := 80, targets := 3 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 7 35 76 265 208 160 96 130 272), lower := (rows 7 35 76 265 208 160 96 130 256), losses := [] }

theorem u32 : Upper (D 7) (R 7) [6,33,72,257,192,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b32 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b33 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 244, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 7 35 76 265 208 160 96 144 258), lower := (rows 7 35 76 265 208 160 96 144 256), losses := [] }

theorem u33 : Upper (D 7) (R 7) [6,33,72,257,192,128,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b33 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b34 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 76 296 145 160 80 130 320), lower := (rows 7 35 76 296 145 160 80 130 256), losses := [] }

theorem u34 : Upper (D 7) (R 7) [6,33,72,288,129,128,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b34 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b35 : PairBound 9 := { available := 2, camps := [{ cop := 1, region := 264, targets := 193 }], pairs := [(3,0),(3,6),(3,7)], upper := (rows 7 35 76 296 145 160 80 192 258), lower := (rows 7 35 76 296 145 160 80 192 256), losses := [] }

theorem u35 : Upper (D 7) (R 7) [6,33,72,288,129,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b35 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b36 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 76 296 146 160 80 129 320), lower := (rows 7 35 76 296 146 160 80 129 256), losses := [] }

theorem u36 : Upper (D 7) (R 7) [6,33,72,288,130,128,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b36 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b37 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 264, targets := 192 },{ cop := 0, region := 208, targets := 1 }], pairs := [(3,6),(3,7),(4,0)], upper := (rows 7 35 76 296 146 160 80 192 257), lower := (rows 7 35 76 296 146 160 80 192 256), losses := [] }

theorem u37 : Upper (D 7) (R 7) [6,33,72,288,130,128,16,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b37 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b38 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 7 35 76 392 146 48 96 129 320), lower := (rows 7 35 76 392 146 48 96 129 256), losses := [] }

theorem u38 : Upper (D 7) (R 7) [6,33,72,384,130,16,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b38 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 460, targets := 2 },{ cop := 0, region := 240, targets := 1 }], pairs := [(2,1),(3,1),(4,0)], upper := (rows 7 35 76 392 146 48 96 192 257), lower := (rows 7 35 76 392 146 48 96 192 256), losses := [] }

theorem u39 : Upper (D 7) (R 7) [6,33,72,384,130,16,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b40 : PairBound 9 := { available := 128, camps := [{ cop := 2, region := 272, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 35 196 26 336 40 96 129 384), lower := (rows 7 35 196 26 336 40 96 129 256), losses := [] }

theorem u40 : Upper (D 7) (R 7) [6,33,192,18,320,8,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b40 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b41 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 312, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 7 35 196 88 176 288 66 129 264), lower := (rows 7 35 196 88 176 288 66 129 256), losses := [] }

theorem u41 : Upper (D 7) (R 7) [6,33,192,80,160,256,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b41 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b42 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 220, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 196 88 176 288 66 136 257), lower := (rows 7 35 196 88 176 288 66 136 256), losses := [] }

theorem u42 : Upper (D 7) (R 7) [6,33,192,80,160,256,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b42 [(5,8),(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b43 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 263, targets := 192 }], pairs := [(0,6),(0,7),(1,6)], upper := (rows 7 35 261 74 176 96 192 136 272), lower := (rows 7 35 261 74 176 96 192 136 256), losses := [] }

theorem u43 : Upper (D 7) (R 7) [6,33,257,66,160,64,128,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b43 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b44 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 261, targets := 96 }], pairs := [(0,5),(0,6),(2,5)], upper := (rows 7 35 261 74 176 96 192 144 264), lower := (rows 7 35 261 74 176 96 192 144 256), losses := [] }

theorem u44 : Upper (D 7) (R 7) [6,33,257,66,160,64,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b44 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b45 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 324 25 208 160 66 136 288), lower := (rows 7 35 324 25 208 160 66 136 256), losses := [] }

theorem u45 : Upper (D 7) (R 7) [6,33,320,17,192,128,2,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b45 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b46 : PairBound 9 := { available := 8, camps := [{ cop := 2, region := 176, targets := 3 },{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6),(1,6),(4,0),(4,1)], upper := (rows 7 35 324 25 208 160 66 160 264), lower := (rows 7 35 324 25 208 160 66 160 256), losses := [] }

theorem u46 : Upper (D 7) (R 7) [6,33,320,17,192,128,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b46 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b47 : PairBound 9 := { available := 128, camps := [{ cop := 4, region := 260, targets := 35 }], pairs := [(2,0),(2,1),(2,5)], upper := (rows 7 35 324 26 208 40 96 129 384), lower := (rows 7 35 324 26 208 40 96 129 256), losses := [] }

theorem u47 : Upper (D 7) (R 7) [6,33,320,18,192,8,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b47 [(5,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b48 : PairBound 9 := { available := 8, camps := [{ cop := 3, region := 260, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 35 324 88 145 160 96 130 264), lower := (rows 7 35 324 88 145 160 96 130 256), losses := [] }

theorem u48 : Upper (D 7) (R 7) [6,33,320,80,129,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b48 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b49 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 327, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 35 324 88 145 160 96 136 258), lower := (rows 7 35 324 88 145 160 96 136 256), losses := [] }

theorem u49 : Upper (D 7) (R 7) [6,33,320,80,129,128,32,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b49 [(7,3)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b50 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 0, region := 200, targets := 32 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(3,5),(4,0)], upper := (rows 7 42 21 73 336 160 192 130 288), lower := (rows 7 42 21 73 336 160 192 130 256), losses := [] }

theorem u50 : Upper (D 7) (R 7) [6,40,17,65,320,128,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b50 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b51 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 434, targets := 1 },{ cop := 0, region := 232, targets := 2 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(3,1),(4,0)], upper := (rows 7 42 21 73 336 160 192 160 258), lower := (rows 7 42 21 73 336 160 192 160 256), losses := [] }

theorem u51 : Upper (D 7) (R 7) [6,40,17,65,320,128,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b51 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b52 : PairBound 9 := { available := 128, camps := [{ cop := 3, region := 272, targets := 35 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(4,0),(4,1),(4,5)], upper := (rows 7 42 21 200 336 33 96 130 384), lower := (rows 7 42 21 200 336 33 96 130 256), losses := [] }

theorem u52 : Upper (D 7) (R 7) [6,40,17,192,320,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b52 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b53 : PairBound 9 := { available := 128, camps := [{ cop := 4, region := 264, targets := 35 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(3,0),(3,1),(3,5)], upper := (rows 7 42 21 328 208 33 96 130 384), lower := (rows 7 42 21 328 208 33 96 130 256), losses := [] }

theorem u53 : Upper (D 7) (R 7) [6,40,17,320,192,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b53 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b54 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 213, targets := 32 },{ cop := 5, region := 330, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,5)], upper := (rows 7 42 21 328 208 160 66 129 288), lower := (rows 7 42 21 328 208 160 66 129 256), losses := [] }

theorem u54 : Upper (D 7) (R 7) [6,40,17,320,192,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b54 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b55 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 0, region := 328, targets := 32 }], pairs := [(1,0),(3,0),(3,5),(4,0)], upper := (rows 7 42 21 328 208 160 66 160 257), lower := (rows 7 42 21 328 208 160 66 160 256), losses := [] }

theorem u55 : Upper (D 7) (R 7) [6,40,17,320,192,128,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b55 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b56 : PairBound 9 := { available := 2, camps := [{ cop := 6, region := 266, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 21 328 208 160 96 129 258), lower := (rows 7 42 21 328 208 160 96 129 256), losses := [] }

theorem u56 : Upper (D 7) (R 7) [6,40,17,320,192,128,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b56 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b57 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,0),(1,6),(3,0),(4,0)], upper := (rows 7 42 21 328 208 160 96 130 257), lower := (rows 7 42 21 328 208 160 96 130 256), losses := [] }

theorem u57 : Upper (D 7) (R 7) [6,40,17,320,192,128,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b57 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b58 : PairBound 9 := { available := 128, camps := [{ cop := 3, region := 272, targets := 35 },{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5),(4,0),(4,1),(4,5)], upper := (rows 7 42 52 200 336 33 66 129 384), lower := (rows 7 42 52 200 336 33 66 129 256), losses := [] }

theorem u58 : Upper (D 7) (R 7) [6,40,48,192,320,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b58 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b59 : PairBound 9 := { available := 128, camps := [{ cop := 4, region := 264, targets := 35 },{ cop := 0, region := 208, targets := 32 }], pairs := [(3,0),(3,1),(3,5),(4,5)], upper := (rows 7 42 52 328 208 33 66 129 384), lower := (rows 7 42 52 328 208 33 66 129 256), losses := [] }

theorem u59 : Upper (D 7) (R 7) [6,40,48,320,192,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b59 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u59
end Delivery.IrregularNine14.P07

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

def b60 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 266, targets := 192 }], pairs := [(1,6),(1,7),(3,6),(3,7)], upper := (rows 7 42 69 266 176 96 192 129 272), lower := (rows 7 42 69 266 176 96 192 129 256), losses := [] }

theorem u60 : Upper (D 7) (R 7) [6,40,65,258,160,64,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b60 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b61 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 69 266 176 96 192 144 257), lower := (rows 7 42 69 266 176 96 192 144 256), losses := [] }

theorem u61 : Upper (D 7) (R 7) [6,40,65,258,160,64,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b61 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b62 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 3, region := 372, targets := 2 }], pairs := [(2,1),(4,0),(4,6)], upper := (rows 7 42 84 137 176 288 65 130 320), lower := (rows 7 42 84 137 176 288 65 130 256), losses := [] }

theorem u62 : Upper (D 7) (R 7) [6,40,80,129,160,256,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b62 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b63 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 306, targets := 65 }], pairs := [(1,0),(1,6),(4,0)], upper := (rows 7 42 84 137 176 288 65 192 258), lower := (rows 7 42 84 137 176 288 65 192 256), losses := [] }

theorem u63 : Upper (D 7) (R 7) [6,40,80,129,160,256,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b63 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b64 : PairBound 9 := { available := 64, camps := [{ cop := 3, region := 374, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 7 42 84 137 176 288 66 129 320), lower := (rows 7 42 84 137 176 288 66 129 256), losses := [] }

theorem u64 : Upper (D 7) (R 7) [6,40,80,129,160,256,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b64 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b65 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 3, region := 290, targets := 64 }], pairs := [(1,6),(2,0),(4,0)], upper := (rows 7 42 84 137 176 288 66 192 257), lower := (rows 7 42 84 137 176 288 66 192 256), losses := [] }

theorem u65 : Upper (D 7) (R 7) [6,40,80,129,160,256,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b65 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b66 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 138, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 138 400 33 65 160 320), lower := (rows 7 42 84 138 400 33 65 160 256), losses := [] }

theorem u66 : Upper (D 7) (R 7) [6,40,80,130,384,1,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b66 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b67 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(2,1),(3,5),(4,1)], upper := (rows 7 42 84 138 400 33 65 192 288), lower := (rows 7 42 84 138 400 33 65 192 256), losses := [{ target := 0, region := (rows 0 34 68 9 25 32 64 196 290), good := (rows 414 314 212 410 400 314 220 196 256) }] }

theorem u67 : Upper (D 7) (R 7) [6,40,80,130,384,1,1,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b67 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b68 : PairBound 9 := { available := 64, camps := [{ cop := 2, region := 171, targets := 64 },{ cop := 0, region := 500, targets := 2 }], pairs := [(0,6),(1,6),(2,1),(3,6)], upper := (rows 7 42 84 138 400 33 96 129 320), lower := (rows 7 42 84 138 400 33 96 129 256), losses := [] }

theorem u68 : Upper (D 7) (R 7) [6,40,80,130,384,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b68 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b69 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 84 138 400 33 96 192 257), lower := (rows 7 42 84 138 400 33 96 192 256), losses := [] }

theorem u69 : Upper (D 7) (R 7) [6,40,80,130,384,1,32,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b69 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b70 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 136, targets := 32 },{ cop := 0, region := 136, targets := 64 }], pairs := [(2,1),(3,5),(3,6),(4,1)], upper := (rows 7 42 84 138 400 96 65 129 288), lower := (rows 7 42 84 138 400 96 65 129 256), losses := [] }

theorem u70 : Upper (D 7) (R 7) [6,40,80,130,384,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b70 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b71 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 138, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 138 400 96 65 160 257), lower := (rows 7 42 84 138 400 96 65 160 256), losses := [] }

theorem u71 : Upper (D 7) (R 7) [6,40,80,130,384,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b71 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b72 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 0, region := 200, targets := 32 }], pairs := [(3,0),(3,5),(4,1),(4,6)], upper := (rows 7 42 84 200 400 33 66 129 288), lower := (rows 7 42 84 200 400 33 66 129 256), losses := [{ target := 0, region := (rows 0 2 4 136 16 32 67 128 290), good := (rows 326 362 84 200 408 352 322 200 256) }] }

theorem u72 : Upper (D 7) (R 7) [6,40,80,192,384,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b72 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b73 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 7 42 84 200 400 33 66 160 257), lower := (rows 7 42 84 200 400 33 66 160 256), losses := [] }

theorem u73 : Upper (D 7) (R 7) [6,40,80,192,384,1,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b73 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b74 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(2,0),(3,1),(4,5),(4,6)], upper := (rows 7 42 84 200 400 33 96 129 258), lower := (rows 7 42 84 200 400 33 96 129 256), losses := [{ target := 0, region := (rows 0 2 12 8 144 32 98 128 259), good := (rows 326 366 84 220 400 352 96 400 256) }] }

theorem u74 : Upper (D 7) (R 7) [6,40,80,192,384,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b74 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b75 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 202, targets := 1 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,0),(3,0),(4,5),(4,6)], upper := (rows 7 42 84 200 400 33 96 130 257), lower := (rows 7 42 84 200 400 33 96 130 256), losses := [] }

theorem u75 : Upper (D 7) (R 7) [6,40,80,192,384,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b75 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b76 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 334, targets := 1 },{ cop := 0, region := 176, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 42 84 392 176 33 66 129 320), lower := (rows 7 42 84 392 176 33 66 129 256), losses := [] }

theorem u76 : Upper (D 7) (R 7) [6,40,80,384,160,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b76 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b77 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 212, targets := 1 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,0),(3,1),(3,5),(4,0)], upper := (rows 7 42 84 392 176 33 66 192 257), lower := (rows 7 42 84 392 176 33 66 192 256), losses := [{ target := 1, region := (rows 1 0 4 25 17 33 64 196 289), good := (rows 445 296 220 392 440 313 192 192 256) }] }

theorem u77 : Upper (D 7) (R 7) [6,40,80,384,160,1,2,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b77 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b78 : PairBound 9 := { available := 2, camps := [{ cop := 4, region := 266, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 392 176 96 65 129 258), lower := (rows 7 42 84 392 176 96 65 129 256), losses := [] }

theorem u78 : Upper (D 7) (R 7) [6,40,80,384,160,64,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b78 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b79 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 392, targets := 64 }], pairs := [(3,5),(3,6),(4,0),(4,6)], upper := (rows 7 42 84 392 176 96 65 130 257), lower := (rows 7 42 84 392 176 96 65 130 256), losses := [] }

theorem u79 : Upper (D 7) (R 7) [6,40,80,384,160,64,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b79 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b80 : PairBound 9 := { available := 64, camps := [{ cop := 4, region := 328, targets := 35 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1),(3,0),(3,1),(3,5)], upper := (rows 7 42 100 280 146 33 192 129 320), lower := (rows 7 42 100 280 146 33 192 129 256), losses := [] }

theorem u80 : Upper (D 7) (R 7) [6,40,96,272,130,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b80 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b81 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(3,5),(4,0),(4,5)], upper := (rows 7 42 100 280 146 33 192 192 257), lower := (rows 7 42 100 280 146 33 192 192 256), losses := [] }

theorem u81 : Upper (D 7) (R 7) [6,40,96,272,130,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b81 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b82 : PairBound 9 := { available := 32, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 25 82 160 320 129 288), lower := (rows 7 42 196 25 82 160 320 129 256), losses := [] }

theorem u82 : Upper (D 7) (R 7) [6,40,192,17,66,128,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b82 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b83 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 42 196 25 82 160 320 160 257), lower := (rows 7 42 196 25 82 160 320 160 256), losses := [] }

theorem u83 : Upper (D 7) (R 7) [6,40,192,17,66,128,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b83 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b84 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 336, targets := 129 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,7)], upper := (rows 7 42 196 25 336 160 66 129 288), lower := (rows 7 42 196 25 336 160 66 129 256), losses := [] }

theorem u84 : Upper (D 7) (R 7) [6,40,192,17,320,128,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b84 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b85 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 42 196 25 336 160 66 160 257), lower := (rows 7 42 196 25 336 160 66 160 256), losses := [] }

theorem u85 : Upper (D 7) (R 7) [6,40,192,17,320,128,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b85 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b86 : PairBound 9 := { available := 32, camps := [{ cop := 1, region := 272, targets := 193 },{ cop := 4, region := 197, targets := 32 }], pairs := [(0,5),(4,0),(4,6),(4,7)], upper := (rows 7 42 196 88 274 160 65 129 288), lower := (rows 7 42 196 88 274 160 65 129 256), losses := [] }

theorem u86 : Upper (D 7) (R 7) [6,40,192,80,258,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b86 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b87 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 344, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 42 196 88 274 160 65 160 257), lower := (rows 7 42 196 88 274 160 65 160 256), losses := [] }

theorem u87 : Upper (D 7) (R 7) [6,40,192,80,258,128,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b87 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b88 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(4,1),(4,6)], upper := (rows 7 42 196 88 400 33 66 129 288), lower := (rows 7 42 196 88 400 33 66 129 256), losses := [] }

theorem u88 : Upper (D 7) (R 7) [6,40,192,80,384,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b88 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b89 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(2,1),(4,1),(4,6)], upper := (rows 7 42 196 88 400 33 66 160 257), lower := (rows 7 42 196 88 400 33 66 160 256), losses := [{ target := 1, region := (rows 1 0 68 76 179 33 64 163 289), good := (rows 445 440 220 92 400 433 220 432 256) }] }

theorem u89 : Upper (D 7) (R 7) [6,40,192,80,384,1,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b89 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b90 : PairBound 9 := { available := 2, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,0),(2,1),(4,5),(4,6)], upper := (rows 7 42 196 88 400 33 96 129 258), lower := (rows 7 42 196 88 400 33 96 129 256), losses := [{ target := 0, region := (rows 0 34 4 13 148 32 98 128 355), good := (rows 350 362 476 344 400 362 354 408 256) }] }

theorem u90 : Upper (D 7) (R 7) [6,40,192,80,384,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b90 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b91 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 },{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(2,1),(4,5),(4,6)], upper := (rows 7 42 196 88 400 33 96 130 257), lower := (rows 7 42 196 88 400 33 96 130 256), losses := [{ target := 1, region := (rows 1 0 132 8 16 33 99 128 289), good := (rows 357 360 196 88 404 353 352 196 256) }] }

theorem u91 : Upper (D 7) (R 7) [6,40,192,80,384,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b91 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b92 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 266, targets := 193 }], pairs := [(1,0),(1,6),(1,7),(3,0)], upper := (rows 7 42 196 266 112 160 65 129 272), lower := (rows 7 42 196 266 112 160 65 129 256), losses := [] }

theorem u92 : Upper (D 7) (R 7) [6,40,192,258,96,128,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b92 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b93 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 196 266 112 160 65 144 257), lower := (rows 7 42 196 266 112 160 65 144 256), losses := [] }

theorem u93 : Upper (D 7) (R 7) [6,40,192,258,96,128,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b93 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b94 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 334, targets := 1 },{ cop := 0, region := 176, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 42 196 328 176 33 66 129 272), lower := (rows 7 42 196 328 176 33 66 129 256), losses := [] }

theorem u94 : Upper (D 7) (R 7) [6,40,192,320,160,1,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b94 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b95 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 196 328 176 33 66 144 257), lower := (rows 7 42 196 328 176 33 66 144 256), losses := [] }

theorem u95 : Upper (D 7) (R 7) [6,40,192,320,160,1,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b95 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b96 : PairBound 9 := { available := 32, camps := [{ cop := 5, region := 260, targets := 131 },{ cop := 0, region := 152, targets := 32 }], pairs := [(2,0),(2,1),(2,7),(3,5)], upper := (rows 7 42 324 25 146 96 192 129 288), lower := (rows 7 42 324 25 146 96 192 129 256), losses := [] }

theorem u96 : Upper (D 7) (R 7) [6,40,320,17,130,64,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b96 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b97 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 333, targets := 32 },{ cop := 3, region := 226, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(3,5)], upper := (rows 7 42 324 25 146 96 192 160 257), lower := (rows 7 42 324 25 146 96 192 160 256), losses := [] }

theorem u97 : Upper (D 7) (R 7) [6,40,320,17,130,64,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b97 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b98 : PairBound 9 := { available := 32, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6),(3,5),(4,5)], upper := (rows 7 42 324 73 146 48 192 129 288), lower := (rows 7 42 324 73 146 48 192 129 256), losses := [] }

theorem u98 : Upper (D 7) (R 7) [6,40,320,65,130,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b98 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b99 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 260, targets := 162 }], pairs := [(2,1),(2,5),(2,7)], upper := (rows 7 42 324 73 146 48 192 160 257), lower := (rows 7 42 324 73 146 48 192 160 256), losses := [] }

theorem u99 : Upper (D 7) (R 7) [6,40,320,65,130,16,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b99 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b100 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 260, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 324 138 112 33 192 129 272), lower := (rows 7 42 324 138 112 33 192 129 256), losses := [] }

theorem u100 : Upper (D 7) (R 7) [6,40,320,130,96,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b100 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b101 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 324 138 112 33 192 144 257), lower := (rows 7 42 324 138 112 33 192 144 256), losses := [] }

theorem u101 : Upper (D 7) (R 7) [6,40,320,130,96,1,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b101 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b102 : PairBound 9 := { available := 32, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 324 138 145 96 65 144 288), lower := (rows 7 42 324 138 145 96 65 144 256), losses := [] }

theorem u102 : Upper (D 7) (R 7) [6,40,320,130,129,64,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b102 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b103 : PairBound 9 := { available := 16, camps := [{ cop := 5, region := 138, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 324 138 145 96 65 160 272), lower := (rows 7 42 324 138 145 96 65 160 256), losses := [] }

theorem u103 : Upper (D 7) (R 7) [6,40,320,130,129,64,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b103 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b104 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 260, targets := 163 }], pairs := [(2,0),(2,1),(2,5),(2,7)], upper := (rows 7 42 324 138 208 33 96 129 272), lower := (rows 7 42 324 138 208 33 96 129 256), losses := [] }

theorem u104 : Upper (D 7) (R 7) [6,40,320,130,192,1,32,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b104 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b105 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 144, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 7 42 324 138 208 33 96 144 257), lower := (rows 7 42 324 138 208 33 96 144 256), losses := [] }

theorem u105 : Upper (D 7) (R 7) [6,40,320,130,192,1,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b105 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b106 : PairBound 9 := { available := 16, camps := [{ cop := 4, region := 364, targets := 2 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(3,1)], upper := (rows 7 42 324 200 145 33 96 130 272), lower := (rows 7 42 324 200 145 33 96 130 256), losses := [] }

theorem u106 : Upper (D 7) (R 7) [6,40,320,192,129,1,32,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b106 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b107 : PairBound 9 := { available := 2, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 324 200 145 33 96 144 258), lower := (rows 7 42 324 200 145 33 96 144 256), losses := [] }

theorem u107 : Upper (D 7) (R 7) [6,40,320,192,129,1,32,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b107 [(7,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b108 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 157, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 13 56 146 288 192 129 320), lower := (rows 7 98 13 56 146 288 192 129 256), losses := [] }

theorem u108 : Upper (D 7) (R 7) [6,96,9,48,130,256,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b108 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b109 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 301, targets := 192 }], pairs := [(0,6),(0,7),(2,6)], upper := (rows 7 98 13 56 146 288 192 192 257), lower := (rows 7 98 13 56 146 288 192 192 256), losses := [] }

theorem u109 : Upper (D 7) (R 7) [6,96,9,48,130,256,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b109 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b110 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 314, targets := 1 },{ cop := 6, region := 34, targets := 128 }], pairs := [(1,0),(1,7),(3,0),(4,0)], upper := (rows 7 98 13 152 304 34 192 129 320), lower := (rows 7 98 13 152 304 34 192 129 256), losses := [] }

theorem u110 : Upper (D 7) (R 7) [6,96,9,144,288,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b110 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b111 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 0, region := 304, targets := 64 }], pairs := [(1,0),(3,0),(4,0),(4,6)], upper := (rows 7 98 13 152 304 34 192 192 257), lower := (rows 7 98 13 152 304 34 192 192 256), losses := [] }

theorem u111 : Upper (D 7) (R 7) [6,96,9,144,288,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b111 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b112 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 141, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 7 98 13 168 274 48 192 129 320), lower := (rows 7 98 13 168 274 48 192 129 256), losses := [] }

theorem u112 : Upper (D 7) (R 7) [6,96,9,160,258,16,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b112 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b113 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 98 13 168 274 48 192 192 257), lower := (rows 7 98 13 168 274 48 192 192 256), losses := [] }

theorem u113 : Upper (D 7) (R 7) [6,96,9,160,258,16,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b113 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b114 : PairBound 9 := { available := 64, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 4, region := 328, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 13 280 176 33 192 130 320), lower := (rows 7 98 13 280 176 33 192 130 256), losses := [] }

theorem u114 : Upper (D 7) (R 7) [6,96,9,272,160,1,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b114 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b115 : PairBound 9 := { available := 2, camps := [{ cop := 5, region := 474, targets := 1 },{ cop := 0, region := 240, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 7 98 13 280 176 33 192 192 258), lower := (rows 7 98 13 280 176 33 192 192 256), losses := [] }

theorem u115 : Upper (D 7) (R 7) [6,96,9,272,160,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b115 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b116 : PairBound 9 := { available := 64, camps := [{ cop := 6, region := 314, targets := 1 },{ cop := 4, region := 328, targets := 2 }], pairs := [(1,0),(3,0),(3,1),(4,0)], upper := (rows 7 98 13 280 176 34 192 129 320), lower := (rows 7 98 13 280 176 34 192 129 256), losses := [] }

theorem u116 : Upper (D 7) (R 7) [6,96,9,272,160,2,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b116 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b117 : PairBound 9 := { available := 1, camps := [{ cop := 8, region := 250, targets := 1 },{ cop := 1, region := 144, targets := 2 }], pairs := [(1,0),(3,0),(4,0),(4,1)], upper := (rows 7 98 13 280 176 34 192 192 257), lower := (rows 7 98 13 280 176 34 192 192 256), losses := [] }

theorem u117 : Upper (D 7) (R 7) [6,96,9,272,160,2,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b117 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b118 : PairBound 9 := { available := 64, camps := [{ cop := 1, region := 272, targets := 129 },{ cop := 0, region := 496, targets := 2 },{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5),(4,0),(4,1),(4,7)], upper := (rows 7 98 28 138 304 33 192 129 320), lower := (rows 7 98 28 138 304 33 192 129 256), losses := [] }

theorem u118 : Upper (D 7) (R 7) [6,96,24,130,288,1,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b118 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b119 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 309, targets := 192 }], pairs := [(0,6),(0,7),(2,6),(2,7)], upper := (rows 7 98 28 138 304 33 192 192 257), lower := (rows 7 98 28 138 304 33 192 192 256), losses := [] }

theorem u119 : Upper (D 7) (R 7) [6,96,24,130,288,1,128,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b119 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u119
end Delivery.IrregularNine14.P07
